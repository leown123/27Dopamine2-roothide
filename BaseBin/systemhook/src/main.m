#include "common.h"
#include "roothider.h"

#import <Foundation/Foundation.h>

#include <mach-o/dyld.h>
#include <mach-o/dyld_images.h>
#include <mach-o/getsect.h>
#include <dlfcn.h>
#include <sys/stat.h>
#include <paths.h>
#include <util.h>
#include <ptrauth.h>
#include <libjailbreak/jbclient_xpc.h>
#include <libjailbreak/codesign.h>
#include <libjailbreak/jbroot.h>
#include "../dyldhook/src/dyld_jbinfo.h"
#include "litehook.h"
#include "sandbox.h"
#include "private.h"

#include <unistd.h>

#import <objc/runtime.h>
#import <UIKit/UIKit.h>

//#include <substrate.h>
#import "fishhook.h"

#import <sys/utsname.h>
#import <sys/sysctl.h>

#import "dobby.h"

#import <sys/fcntl.h>

#import <stdio.h>

#include<pthread.h>

bool gFullyDebugged = false;
static void *gLibSandboxHandle;
char *JB_BootUUID = NULL;
char *JB_RootPath = NULL;
char *get_jbroot(void) { return JB_RootPath; }

static char gExecutablePath[PATH_MAX];
static int load_executable_path(void)
{
	char executablePath[PATH_MAX];
	uint32_t bufsize = PATH_MAX;
	if (_NSGetExecutablePath(executablePath, &bufsize) == 0) {
		if (realpath(executablePath, gExecutablePath) != NULL) return 0;
	}
	return -1;
}

static char *JB_SandboxExtensions = NULL;

void consume_tokenized_sandbox_extensions(char *sandboxExtensions)
{
	if (sandboxExtensions[0] == '\0') return;

	char *it = sandboxExtensions;
	char *last = sandboxExtensions;
	while (*(++it) != '\0') {
		if (*it == '|') {
			*it = '\0';
			sandbox_extension_consume(last);
			last = &it[1];
			*it = '|';
		}
	}
	sandbox_extension_consume(last);
}

void *(*sandbox_apply_orig)(void *) = NULL;
void *sandbox_apply_hook(void *a1)
{
	void *r = sandbox_apply_orig(a1);
	consume_tokenized_sandbox_extensions(JB_SandboxExtensions);
	return r;
}

int dyld_hook_routine(void **dyld, int idx, void *hook, void **orig, uint16_t pacSalt)
{
	if (!dyld) return -1;

	uint64_t dyldPacDiversifier = ((uint64_t)dyld & ~(0xFFFFull << 48)) | (0x63FAull << 48);
	void **dyldFuncPtrs = ptrauth_auth_data(*dyld, ptrauth_key_process_independent_data, dyldPacDiversifier);
	if (!dyldFuncPtrs) return -1;

	if (vm_protect(mach_task_self_, (mach_vm_address_t)&dyldFuncPtrs[idx], sizeof(void *), false, VM_PROT_READ | VM_PROT_WRITE) == 0) {
		uint64_t location = (uint64_t)&dyldFuncPtrs[idx];
		uint64_t pacDiversifier = (location & ~(0xFFFFull << 48)) | ((uint64_t)pacSalt << 48);

		*orig = ptrauth_auth_and_resign(dyldFuncPtrs[idx], ptrauth_key_process_independent_code, pacDiversifier, ptrauth_key_function_pointer, 0);
		dyldFuncPtrs[idx] = ptrauth_auth_and_resign(hook, ptrauth_key_function_pointer, 0, ptrauth_key_process_independent_code, pacDiversifier);
		vm_protect(mach_task_self_, (mach_vm_address_t)&dyldFuncPtrs[idx], sizeof(void *), false, VM_PROT_READ);
		return 0;
	}

	return -1;
}

// dlsym calls use __builtin_return_address(0) to determine what library called it
// Since we hook them, if we just call the original function on our own, the return address will always point to systemhook
// Therefore we must ensure the call to the original function is a tail call, which ensures that the stack and lr are restored and the compiler turns the call into a direct branch
// This is done via __attribute__((musttail)), this way __builtin_return_address(0) will point to the original calling library instead of systemhook

void *(*dyld_dlsym_orig)(void *dyld, void *handle, const char *name);
void *dyld_dlsym_hook(void *dyld, void *handle, const char *name)
{
	if (handle == gLibSandboxHandle && !strcmp(name, "sandbox_apply")) {
		// We abuse the fact that libsystem_sandbox will call dlsym to get the sandbox_apply pointer here
		// Because we can just return a different pointer, we avoid doing instruction replacements
		return sandbox_apply_hook;
	}
	__attribute__((musttail)) return dyld_dlsym_orig(dyld, handle, name);
}

int ptrace_hook(int request, pid_t pid, caddr_t addr, int data)
{
	int r = syscall(SYS_ptrace, request, pid, addr, data);

	// ptrace works on any process when the caller is unsandboxed,
	// but when the victim process does not have the get-task-allow entitlement,
	// it will fail to set the debug flags, therefore we patch ptrace to manually apply them
	// processes that have tweak injection enabled will have their debug flags already set
	// this is only relevant for ones that don't, e.g. if you disable tweak injection on an app via choicy
	// but still want to be able to attach a debugger to them
	if (r == 0 && (request == PT_ATTACHEXC || request == PT_ATTACH)) {
		jbclient_platform_set_process_debugged(pid, true);
		jbclient_platform_set_process_debugged(getpid(), true);
	}

	return r;
}

#ifndef __arm64e__

// The NECP subsystem is the only thing in the kernel that ever checks CS_VALID on userspace processes (Only on iOS >=16)
// In order to not break system functionality, we need to readd CS_VALID before any of these are invoked

int necp_match_policy_hook(uint8_t *parameters, size_t parameters_size, void *returned_result)
{
	jbclient_cs_revalidate();
	return syscall(SYS_necp_match_policy, parameters, parameters_size, returned_result);
}

int necp_open_hook(int flags)
{
	jbclient_cs_revalidate();
	return syscall(SYS_necp_open, flags);
}

int necp_client_action_hook(int necp_fd, uint32_t action, uuid_t client_id, size_t client_id_len, uint8_t *buffer, size_t buffer_size)
{
	jbclient_cs_revalidate();
	return syscall(SYS_necp_client_action, necp_fd, action, client_id, client_id_len, buffer, buffer_size);
}

int necp_session_open_hook(int flags)
{
	jbclient_cs_revalidate();
	return syscall(SYS_necp_session_open, flags);
}

int necp_session_action_hook(int necp_fd, uint32_t action, uint8_t *in_buffer, size_t in_buffer_length, uint8_t *out_buffer, size_t out_buffer_length)
{
	jbclient_cs_revalidate();
	return syscall(SYS_necp_session_action, necp_fd, action, in_buffer, in_buffer_length, out_buffer, out_buffer_length);
}

// For the userland, there are multiple processes that will check CS_VALID for one reason or another
// As we inject system wide (or at least almost system wide), we can just patch the source of the info though - csops itself
// Additionally we also remove CS_DEBUGGED while we're at it, as on arm64e this also is not set and everything is fine
// That way we have unified behaviour between both arm64 and arm64e

int csops_hook(pid_t pid, unsigned int ops, void *useraddr, size_t usersize)
{
	int rv = syscall(SYS_csops, pid, ops, useraddr, usersize);
	if (rv != 0) return rv;
	if (ops == CS_OPS_STATUS) {
		if (useraddr && usersize == sizeof(uint32_t)) {
			uint32_t* csflag = (uint32_t *)useraddr;
			*csflag |= CS_VALID;
			*csflag &= ~CS_DEBUGGED;
			if (pid == getpid() && gFullyDebugged) {
				*csflag |= CS_DEBUGGED;
			}
		}
	}
	return rv;
}

int csops_audittoken_hook(pid_t pid, unsigned int ops, void *useraddr, size_t usersize, audit_token_t *token)
{
	int rv = syscall(SYS_csops_audittoken, pid, ops, useraddr, usersize, token);
	if (rv != 0) return rv;
	if (ops == CS_OPS_STATUS) {
		if (useraddr && usersize == sizeof(uint32_t)) {
			uint32_t* csflag = (uint32_t *)useraddr;
			*csflag |= CS_VALID;
			*csflag &= ~CS_DEBUGGED;
			if (pid == getpid() && gFullyDebugged) {
				*csflag |= CS_DEBUGGED;
			}
		}
	}
	return rv;
}

#endif

bool should_enable_tweaks(void)
{
	if (access(JBROOT_PATH("/basebin/.safe_mode"), F_OK) == 0) {
		return false;
	}

	char *tweaksDisabledEnv = getenv("DISABLE_TWEAKS");
	if (tweaksDisabledEnv) {
		if (!strcmp(tweaksDisabledEnv, "1")) {
			return false;
		}
	}


/******************* roothide specific ***************/
const char *safeModeValue = getenv("_SafeMode");
if (safeModeValue) {
	if (!strcmp(safeModeValue, "1")) {
		return false;
	}
}
const char *msSafeModeValue = getenv("_MSSafeMode");
if (msSafeModeValue) {
	if (!strcmp(msSafeModeValue, "1")) {
		return false;
	}
}
/******************* roothide specific *************/


	const char *tweaksDisabledPathSuffixes[] = {
		// System binaries
		"/usr/libexec/xpcproxy",

		// Dopamine app itself (jailbreak detection bypass tweaks can break it)
		"Dopamine.app/Dopamine",
	};
	for (size_t i = 0; i < sizeof(tweaksDisabledPathSuffixes) / sizeof(const char*); i++) {
		if (string_has_suffix(gExecutablePath, tweaksDisabledPathSuffixes[i])) return false;
	}

	if (__builtin_available(iOS 16.0, *)) {
		// These seem to be problematic on iOS 16+ (dyld gets stuck in a weird way when opening TweakLoader)
		const char *iOS16TweaksDisabledPaths[] = {
			"/usr/libexec/logd",
			"/usr/sbin/notifyd",
			"/usr/libexec/usermanagerd",
		};
		for (size_t i = 0; i < sizeof(iOS16TweaksDisabledPaths) / sizeof(const char*); i++) {
			if (!strcmp(gExecutablePath, iOS16TweaksDisabledPaths[i])) return false;
		}
	}

	return true;
}

int __posix_spawn_hook(pid_t *restrict pid, const char *restrict path, struct _posix_spawn_args_desc *desc, char *const argv[restrict], char * const envp[restrict])
{
	return roothide_systemhook___posix_spawn_prehook(pid, path, desc, argv, envp, (void *)roothide_systemhook___posix_spawn_posthook, jbclient_trust_file_by_path, jbclient_platform_set_process_debugged, jbclient_jbsettings_get_double("jetsamMultiplier"));
}

int __posix_spawn_hook_with_filter(pid_t *restrict pid, const char *restrict path, char *const argv[restrict], char * const envp[restrict], struct _posix_spawn_args_desc *desc, int *ret)
{
	*ret = roothide_systemhook___posix_spawn_prehook(pid, path, desc, argv, envp, (void *)roothide_systemhook___posix_spawn_posthook, jbclient_trust_file_by_path, jbclient_platform_set_process_debugged, jbclient_jbsettings_get_double("jetsamMultiplier"));
	return 1;
}

int __execve_hook(const char *path, char *const argv[], char *const envp[])
{
	return roothide_systemhook___execve_prehook(path, argv, envp, (void *)roothide_systemhook___execve_posthook, jbclient_trust_file_by_path);
}

const struct mach_header_64 *get_dyld_mach_header(void)
{
	static const struct mach_header_64 *dyldMachHeader = NULL;
	static dispatch_once_t onceToken;
	dispatch_once (&onceToken, ^{
		task_dyld_info_data_t dyldInfo;
		uint32_t count = TASK_DYLD_INFO_COUNT;
		kern_return_t kr = task_info(mach_task_self_, TASK_DYLD_INFO, (task_info_t)&dyldInfo, &count);
		if (kr == KERN_SUCCESS) {
			struct dyld_all_image_infos *infos = (struct dyld_all_image_infos *)dyldInfo.all_image_info_addr;
			dyldMachHeader = (const struct mach_header_64 *)infos->dyldImageLoadAddress;
		}
	});
	return dyldMachHeader;
}

int parse_dyldhook_jbinfo(char **jbRootPathOut, char **bootUUIDOut, char **sandboxExtensionsOut, bool *fullyDebuggedOut)
{
	// Get dyld header
	const struct mach_header_64 *dyldHeader = get_dyld_mach_header();
	if (!dyldHeader) return -1;

	// Check if dyld LC_UUID contains dopamine magic
	uuid_t dyldUUID;
	if (!_dyld_get_image_uuid((const struct mach_header *)dyldHeader, dyldUUID)) return -2;
	if (!string_has_prefix((char *)dyldUUID, "DOPA")) return -3;

	// If so, get __jbinfo section
	size_t jbInfoSize = 0;
	struct dyld_jbinfo *jbInfo = (struct dyld_jbinfo *)getsectiondata(dyldHeader, "__DATA", "__jbinfo", &jbInfoSize);
	if (!jbInfo) return -4;

	// Check if dyld already performed check-in
	if (jbInfo->state != DYLD_STATE_CHECKED_IN) return -5;

	// If so, parse jbinfo
	if (jbRootPathOut)        *jbRootPathOut        = jbInfo->jbRootPath;
	if (bootUUIDOut)          *bootUUIDOut          = jbInfo->bootUUID;
	if (sandboxExtensionsOut) *sandboxExtensionsOut = jbInfo->sandboxExtensions;
	if (fullyDebuggedOut)     *fullyDebuggedOut     = jbInfo->fullyDebugged;

	return 0;
}

// ---------- 黑名单路径 ----------
static NSArray *jailbreakPaths = nil;

// ---------- 保存原始函数指针 ----------
// 对于 C 函数，通过 dlsym 获取原始地址（假设未被 litehook 修改符号表）
static int (*orig_access)(const char *, int);
static int (*orig_stat)(const char *, struct stat *);
static int (*orig_lstat)(const char *, struct stat *);
static int (*orig_open)(const char *, int, ...);
static FILE *(*orig_fopen)(const char *, const char *);
static pid_t (*orig_fork)(void);
// 保存原始函数指针
static int (*orig_fstat)(int fd, struct stat *buf);


static char *(*orig_getenv)(const char *);
static const char *(*orig_dyld_get_image_name)(uint32_t);
static void *(*orig_dlopen)(const char *, int);
static void *(*orig_dlsym)(void *, const char *);
static uint32_t (*orig_dyld_image_count)(void);
static int (*orig_dladdr)(const void *addr, Dl_info *info);

// ---------- 原始函数指针 ----------
static int (*orig_stat64)(const char *path, struct stat64 *buf);
static int (*orig_mkdir)(const char *path, mode_t mode);
static int (*orig_rmdir)(const char *path);
static int (*orig_rename)(const char *oldpath, const char *newpath);


// ---------- 辅助函数：检查路径是否在黑名单中 ----------
static BOOL isJailbreakPath(const char *path) {
    if (!path) return NO;
    
    if (!jailbreakPaths)
    {
        jailbreakPaths = @[
                    @"/Applications/Cydia.app",
                    @"/Applications/Sileo.app",
                    @"/Applications/Zebra.app",
                    @"/bin/bash",
                    @"/bin/sh",
                    @"/usr/sbin/sshd",
                    @"/usr/libexec/ssh-keysign",
                    @"/etc/apt",
                    @"/etc/ssh/sshd_config",
                    @"/Library/MobileSubstrate/MobileSubstrate.dylib",
                    @"/Library/MobileSubstrate/DynamicLibraries",
                    @"/var/lib/cydia",
                    @"/var/cache/apt",
                    @"/var/tmp/cydia.log",
                    @"/private/var/lib/apt",
                    @"/private/var/stash",
                    @"systemhook",
                    @"roothide",
					@"basebin",
					@"Troll",
					@"sign",
					@"jb",
					@"libjail",
                ];
    }
    
    NSString *nsPath = [NSString stringWithUTF8String:path];
    for (NSString *black in jailbreakPaths) {
        if ([nsPath hasPrefix:black] || [nsPath isEqualToString:black]) {
            return YES;
        }
    }
    return NO;
}

// ---------- 辅助函数：检查路径是否在反作弊文件中 ----------
static BOOL isdocPath(const char *path) {
    if (!path) return NO;
    
    NSString *nsPath = [NSString stringWithUTF8String:path];
    
    if ([nsPath hasPrefix:@"ano"])//|| [nsPath hasPrefix:@"Library"]
    {
        return YES;
    }
   
    return NO;
}

// ---------- 1. 文件操作类 ----------
int hooked_access(const char *path, int amode) {
	
	
    if (isJailbreakPath(path)) {

		NSLog(@"小罪ADD: hooked_access called ! 命中isJailbreakPath: path:%s",path);
        errno = ENOENT;
        return -1;
    }

	if (isdocPath(path)) {
		NSLog(@"小罪ADD: hooked_access called ! 命中isdocPath: path:%s",path);
        //return 0;
    }
	
    return orig_access(path, amode);
}


// ---------- 钩子函数：stat ----------
int hooked_stat(const char *path, struct stat *buf) {
	int rt = orig_stat(path, buf);
    
    
    if (isJailbreakPath(path)) {
		NSLog(@"小罪ADD: hooked_stat 命中 isJailbreakPath ! path:%s",path);
        errno = ENOENT;
        return -1;
    }

	if (isdocPath(path)) 
	{
		NSLog(@"小罪ADD: hooked_stat 命中 isdocPath ! path:%s",path);
        //return 0;
    }
	
    return rt;
}

// ---------- 钩子函数：lstat ----------
int hooked_lstat(const char *path, struct stat *buf) {

	int rt = orig_lstat(path, buf);
    
    
    if (isJailbreakPath(path)) {
		NSLog(@"小罪ADD: hooked_lstat 命中 isJailbreakPath ! path:%s",path);
        errno = ENOENT;
        return -1;
    }

	if (isdocPath(path)) 
	{
		NSLog(@"小罪ADD: hooked_lstat 命中 isJailbreakPath ! path:%s",path);
        //return 0;
    }

	return rt;

	//return orig_lstat(path, buf);
    //return syscall(190, path, buf);
}

int hooked_open(const char *path, int flags, ...) {
	//NSLog(@"小罪ADD: hooked_open called ! path:%s",path);
	
    if (isJailbreakPath(path)) {
		NSLog(@"小罪ADD: hooked_open 命中 isJailbreakPath ! path:%s",path);
        errno = ENOENT;
        return -1;
    }

	if (isdocPath(path)) {
		NSLog(@"小罪ADD: hooked_open 命中 isdocPath ! path:%s",path);
        //errno = ENOENT;
        //return -1;
    }
	
    // 处理可变参数
    mode_t mode = 0;
    if (flags & O_CREAT) {
        va_list ap;
        va_start(ap, flags);
        mode = va_arg(ap, int);
        va_end(ap);
        return orig_open(path, flags, mode);
    }
    return orig_open(path, flags, mode);
}

FILE *hooked_fopen(const char *filename, const char *mode) {
    // 检查文件路径是否在黑名单中
    if (isJailbreakPath(filename)) 
	{
	NSLog(@"小罪ADD: hooked_fopen 命中 isJailbreakPath ! filename:%s,mode:%s",filename,mode);
        errno = ENOENT;          // 假装文件不存在
        return NULL;
    }

	if (isdocPath(filename)) {
	NSLog(@"小罪ADD: hooked_fopen 命中 isdocPath ! filename:%s,mode:%s",filename,mode);
        //errno = ENOENT;
        //return NULL;
    }
    // 调用原始 fopen
    return orig_fopen(filename, mode);
}



// ---------- 2. 环境变量检测 ----------
static __thread int in_hook = 0;  // 线程局部变量

char *hooked_getenv(const char *name) {

    if (strcmp(name, "DYLD_INSERT_LIBRARIES") == 0) {
        return NULL;
    }
    return orig_getenv(name);
}

// ---------- 3. 动态库检测 ----------
const char *hooked_dyld_get_image_name(uint32_t index) {
    const char *name = orig_dyld_get_image_name(index);
	
    if (name) {
        NSString *nsName = [NSString stringWithUTF8String:name];
        NSArray *blacklistedLibs = @[@"MobileSubstrate", @"Substrate", @"CydiaSubstrate", @"Frida", @"systemhook", @"roothide", @"hook",@"Troll",@"sign",@"jb",@"libjail"];
        for (NSString *lib in blacklistedLibs) {
            if ([nsName containsString:lib]) {
			NSLog(@"小罪ADD: hooked_dyld_get_image_name called 命中 blacklistedLibs! lib:%@ ,name:%s",lib,name);
                //return "/usr/lib/libSystem.B.dylib";
				return "";
            }
        }
    }
    return name;
}

void *hooked_dlsym(void *handle, const char *symbol) {

	//NSLog(@"小罪ADD: hooked_dlsym called ! symbol:%s",symbol);
    if (symbol) {
        NSString *nsSymbol = [NSString stringWithUTF8String:symbol];
        NSArray *blacklistedSymbols = @[@"MSHook", @"Substrate", @"Jailbreak", @"root", @"Root",@"fish",@"systemhook",@"Troll",
@"jb",@"libjail"];
        for (NSString *sym in blacklistedSymbols) {
            if ([nsSymbol containsString:sym]) {
			NSLog(@"小罪ADD: hooked_dlsym called 命中 blacklistedSymbols! symbol:%s,sym:%@",symbol,sym);
                return NULL;
            }
        }
    }
    return orig_dlsym(handle, symbol);
}

pid_t hooked_fork(void) {
NSLog(@"小罪ADD: hooked_fork called !");
    // 某些检测会尝试fork，可返回错误
    errno = EPERM;
    return -1;
}

long selfdylibadd = 0;
long selfdylibend = 0;
long selfdylibsize = 0x20000;

static long Getselfdylibadd() {
    uint32_t count = _dyld_image_count();
    for (int i = 0; i < count; i++) {
        const char * path = (const char *)_dyld_get_image_name(i);
        
        NSString *res = [NSString stringWithUTF8String:path];
        
        long linshiptr = (long)_dyld_get_image_vmaddr_slide(i);
        
        if([res hasSuffix:@"/usr/lib/libswiftPrivate_BiomeStreams.dylib"])// && linshiptr < 0x100000000
        {
            //continue;
            return linshiptr;
        }
    }
    return 0;
}

long 

int hooked_dladdr(const void *addr, Dl_info *info) {

	if(!selfdylibadd || !selfdylibend)
	{
		selfdylibadd = Getselfdylibadd();
		selfdylibend = selfdylibadd + selfdylibsize;
	}

	if((long)addr >= selfdylibadd && addr <= selfdylibend)
	{
		NSLog(@"小罪ADD: hooked_dladdr called 命中 systemhook模块地址! addr:%lx",addr);
		memset(info, 0, sizeof(Dl_info));
        return 0;
	}
		
    // 先调用原始函数获取真实信息
    int ret = orig_dladdr(addr, info);
    
    // 如果原始函数成功返回非0，并且 info 有效
    if (ret != 0 && info) {
        // 检查文件名（dli_fname）是否为越狱相关路径
        if (info->dli_fname && isJailbreakPath(info->dli_fname)) {
			NSLog(@"小罪ADD: hooked_dladdr called 命中 jailbreakPaths! info->dli_fname:%s",info->dli_fname);
            // 伪装成未知符号（返回0表示未找到）
            // 或者可以选择修改信息，例如改为系统库的路径
            memset(info, 0, sizeof(Dl_info));
            return 0;
        }
        
        // 检查符号名（dli_sname）是否包含越狱特征（可选）
        if (info->dli_sname) {
            NSString *sname = [NSString stringWithUTF8String:info->dli_sname];
            NSArray *blacklistedSymbols = @[@"MSHook", @"Substrate", @"dobby", @"jailbreak", @"sb",@"MSHook", @"Jailbreak", @"root", @"Root",@"fish",@"systemhook",@"Troll",
@"jb",@"libjail"];
            for (NSString *black in blacklistedSymbols) {
                if ([sname containsString:black]) {
					NSLog(@"小罪ADD: hooked_dladdr called 命中 blacklistedSymbols! sname:%@,black:%@",sname,black);
                    memset(info, 0, sizeof(Dl_info));
                    return 0;
                }
            }
        }
    }
    
    return ret;
}

// ========== Objective-C 方法 Hook ==========
// 注意：fishhook 只能 hook C 函数，OC 方法需要用 runtime
static IMP orig_fileExistsAtPath;
static IMP orig_fileExistsAtPath_isDirectory;
static IMP orig_canOpenURL;

BOOL hooked_fileExistsAtPath(id self, SEL _cmd, NSString *path) {

	//NSLog(@"小罪ADD: hooked_fileExistsAtPath called ! path:%@",path);
    for (NSString *black in jailbreakPaths) {
        if ([path hasPrefix:black] || [path isEqualToString:black]) {
			NSLog(@"小罪ADD: hooked_fileExistsAtPath called 命中 jailbreakPaths! path:%@",path);
            return NO;
        }
    }

	if(path)
	{
		
		const char* pathstr = [path UTF8String];
	
		if (isJailbreakPath(pathstr)) {
			NSLog(@"小罪ADD: hooked_fileExistsAtPath 命中 isJailbreakPath ! pathstr:%s",pathstr);
	        return NO;
	    }
	
		if (isdocPath(pathstr)) 
		{
			NSLog(@"小罪ADD: hooked_fileExistsAtPath 命中 isdocPath ! pathstr:%s",pathstr);
	        //return YES;
	    }
	}
    return ((BOOL(*)(id, SEL, NSString *))orig_fileExistsAtPath)(self, _cmd, path);
}

BOOL hooked_fileExistsAtPath_isDirectory(id self, SEL _cmd, NSString *path, BOOL *isDirectory) {
//NSLog(@"小罪ADD: hooked_fileExistsAtPath_isDirectory called ! path:%@",path);
    for (NSString *black in jailbreakPaths) {
        if ([path hasPrefix:black] || [path isEqualToString:black]) {
		NSLog(@"小罪ADD: hooked_fileExistsAtPath_isDirectory called 命中 jailbreakPaths! path:%@",path);
            return NO;
        }
    }

	if(path)
	{
		const char* pathstr = [path UTF8String];
	
		if (isJailbreakPath(pathstr)) {
			NSLog(@"小罪ADD: hooked_fileExistsAtPath_isDirectory 命中 isJailbreakPath ! pathstr:%s",pathstr);
	        return NO;
	    }
	
		if (isdocPath(pathstr)) 
		{
			NSLog(@"小罪ADD: hooked_fileExistsAtPath_isDirectory 命中 isdocPath ! pathstr:%s",pathstr);
	        //return YES;
	    }
	}
	
    return ((BOOL(*)(id, SEL, NSString *, BOOL *))orig_fileExistsAtPath_isDirectory)(self, _cmd, path, isDirectory);
}

BOOL hooked_canOpenURL(id self, SEL _cmd, NSURL *url) {
    NSString *scheme = [url scheme];
	NSLog(@"小罪ADD: scheme called ! scheme:%@",scheme);
    if ([scheme hasPrefix:@"cydia"] || [scheme hasPrefix:@"sileo"] || 
        [scheme hasPrefix:@"zebra"] || [scheme hasPrefix:@"filza"] || [scheme hasPrefix:@"Dopamine"]) {
		NSLog(@"小罪ADD: hooked_canOpenURL called 命中 jailbreakPaths! scheme:%@",scheme);
        return NO;
    }
    return ((BOOL(*)(id, SEL, NSURL *))orig_canOpenURL)(self, _cmd, url);
}

// ---------- 原始函数指针 ----------
static int (*orig_uname)(struct utsname *);
static int (*orig_sysctlbyname)(const char *, void *, size_t *, void *, size_t);

// ---------- Hook: uname ----------
int hooked_uname(struct utsname *buf) {

    int ret = orig_uname(buf);
    if (ret == 0 && buf) {
        // 修改系统版本相关字段
        // release: 内核版本，如 "21.0.0"（对应 iOS 21.0）
        strcpy(buf->release, "21.0.0");
        // version: 详细版本信息，可伪造
        strcpy(buf->version, "Darwin Kernel Version 21.0.0: Mon Jan 1 00:00:00 PDT 2024; root:xnu-7192.0.0~1/RELEASE_ARM64_T8101");
        // 其他字段（sysname、machine等）可根据需要保持原样或修改
    }
	//NSLog(@"小罪ADD: hooked_uname called ! buf->release:%s",buf->release);
    return ret;
}

// ---------- Hook: sysctlbyname ----------
int hooked_sysctlbyname(const char *name, void *oldp, size_t *oldlenp, void *newp, size_t newlen) 
{
	//NSLog(@"小罪ADD: hooked_sysctlbyname called ! name:%s",name);

	if (*oldlenp == sizeof(int) && strcmp(name, "security.mac.amfi.developer_mode_status") == 0) 
	{
    	 *(int *)oldp = 0; // 伪装成未开启开发者模式
         return 0;
    }
	
    // 拦截系统版本相关的 sysctl 名称
    if (strcmp(name, "kern.osversion") == 0) {
        // 返回伪造的构建号（例如 iOS 21.0 的构建号）
        const char *fakeBuild = "21A123";
        if (oldp && oldlenp) {
            size_t needed = strlen(fakeBuild) + 1;
            if (*oldlenp >= needed) {
                strcpy((char *)oldp, fakeBuild);
                *oldlenp = needed - 1; // 不包含终止符的长度
                return 0;
            }
        }
        // 如果缓冲区不足，返回错误
        errno = ENOMEM;
        return -1;
    }
    else if (strcmp(name, "kern.version") == 0) {
        // 返回伪造的内核版本信息
        const char *fakeKernVer = "Darwin Kernel Version 21.0.0: root:xnu-7192.0.0~1/RELEASE_ARM64_T8101";
        if (oldp && oldlenp) {
            size_t needed = strlen(fakeKernVer) + 1;
            if (*oldlenp >= needed) {
                strcpy((char *)oldp, fakeKernVer);
                *oldlenp = needed - 1;
                return 0;
            }
        }
        errno = ENOMEM;
        return -1;
    }

	// 处理产品版本号（新增）
    else if (strcmp(name, "kern.osproductversion") == 0) {
        const char *fakeVersion = "21.0"; // 伪装成 iOS 21.0
        size_t needed = strlen(fakeVersion) + 1;
        if (oldp) {
            if (*oldlenp < needed) {
                *oldlenp = needed;
                errno = ENOMEM;
                return -1;
            }
            strcpy((char *)oldp, fakeVersion);
            *oldlenp = needed - 1;
        } else {
            *oldlenp = needed;
        }
        return 0;
    }
	
    // 其他 sysctl 名称正常调用原函数
    return orig_sysctlbyname(name, oldp, oldlenp, newp, newlen);
}

// ---------- Objective-C Runtime Hooks ----------
static IMP orig_UIDevice_systemVersion;
static IMP orig_NSProcessInfo_operatingSystemVersion;
static IMP orig_NSProcessInfo_operatingSystemVersionString;

// Hook [UIDevice systemVersion]
NSString *hooked_UIDevice_systemVersion(id self, SEL _cmd) {
    return @"21.0"; // 直接返回固定版本字符串
}

// Hook [NSProcessInfo operatingSystemVersion]
NSOperatingSystemVersion hooked_NSProcessInfo_operatingSystemVersion(id self, SEL _cmd) {
    NSOperatingSystemVersion version = {21, 0, 0}; // major, minor, patch
    return version;
}

// Hook [NSProcessInfo operatingSystemVersionString]
NSString *hooked_NSProcessInfo_operatingSystemVersionString(id self, SEL _cmd) {
    return @"Version 21.0 (Build 21A123)";
}

// ---------- 1. stat64 Hook ----------
int hooked_stat64(const char *path, struct stat64 *buf) {

	if (isJailbreakPath(path)) {
	NSLog(@"小罪ADD: hooked_stat64 命中 isJailbreakPath ! path:%s",path);
        errno = ENOENT;
        return -1;
    }

	if (isdocPath(path)) {
	NSLog(@"小罪ADD: hooked_stat64 命中 isdocPath ! path:%s",path);
        //errno = ENOENT;
        //return -1;
    }
	
    return orig_stat64(path, buf);
}

// ---------- 2. mkdir Hook ----------
int hooked_mkdir(const char *path, mode_t mode) {
    if (isJailbreakPath(path)) {
		NSLog(@"小罪ADD: hooked_mkdir 命中 isJailbreakPath ! path:%s",path);
        errno = EACCES;  // 权限不足，阻止创建
        return -1;
    }

	if (isdocPath(path)) {
		//NSLog(@"小罪ADD: hooked_mkdir 命中 isdocPath ! path:%s",path);
        //return 0;
    }
	
    return orig_mkdir(path, mode);
}

// ---------- 3. rmdir Hook ----------
int hooked_rmdir(const char *path) {

    if (isJailbreakPath(path)) {
		NSLog(@"小罪ADD: hooked_rmdir 命中 isJailbreakPath ! path:%s",path);
        errno = EACCES;  // 权限不足，阻止创建
        return -1;
    }

	if (isdocPath(path)) {
		//NSLog(@"小罪ADD: hooked_rmdir 命中 isdocPath ! path:%s",path);
        //return 0;
    }
    return orig_rmdir(path);
}

// ---------- 4. rename Hook ----------
int hooked_rename(const char *oldpath, const char *newpath) {
    // 检查旧路径或新路径是否在黑名单中
    if (isJailbreakPath(oldpath) || isJailbreakPath(newpath)) {
        errno = EACCES;
        return -1;
    }

	if (isJailbreakPath(oldpath) || isJailbreakPath(newpath))
	{
		NSLog(@"小罪ADD: hooked_rename 命中 isJailbreakPath ! oldpath:%s , newpath:%s",oldpath,newpath);
        errno = EACCES;  // 权限不足，阻止创建
        return -1;
    }

	if (isdocPath(oldpath) || isdocPath(newpath))
	{
		NSLog(@"小罪ADD: hooked_rename 命中 isdocPath ! oldpath:%s , newpath:%s",oldpath,newpath);
        //return 0;
    }

	
    return orig_rename(oldpath, newpath);
}

void Read_Datanew(long Src,int Size,void* Dst)
{
    vm_copy(mach_task_self(),(vm_address_t)Src,Size,(vm_address_t)Dst);
    return ;
}

long Read_Long(long src)
{
    long Buff=0;
    
    //Buff = read<long>(src);
    Read_Datanew(src,8,&Buff);
    return Buff;
}

static long tersafeadd = 0;
static int tersafesize = 0;
static long tersafebakadd = 0;

static long Get_tersafe_base() {
    uint32_t count = _dyld_image_count();
    for (int i = 0; i < count; i++) {
        const char * path = (const char *)_dyld_get_image_name(i);
        
        NSString *res = [NSString stringWithUTF8String:path];
        
        long linshiptr = (long)_dyld_get_image_vmaddr_slide(i);
        
        if([res hasSuffix:@"tersafe"])// && linshiptr < 0x100000000
        {
            //continue;
            return linshiptr;
        }
    }
    return 0;
}

const char* Get_tersafe_path() {
    uint32_t count = _dyld_image_count();
    for (int i = 0; i < count; i++) {
        const char * path = (const char *)_dyld_get_image_name(i);
        
        NSString *res = [NSString stringWithUTF8String:path];

        if([res hasSuffix:@"tersafe"])// && linshiptr < 0x100000000
        {
            //continue;
            return path;
        }
  
    }
    return 0;
}

long Get_tersafe_bak() 
{
	const char* tersapath = Get_tersafe_path();

	// 1. 读取dylib到本地内存
    int fd = open(tersapath, O_RDONLY);
    if (fd == -1) return 0;
    
    struct stat st;
    fstat(fd, &st);
    size_t file_size = st.st_size;

	tersafesize = file_size;
    
    // 2. 在本地创建匿名映射
    void* local_map = mmap(NULL, file_size, 
                          PROT_READ | PROT_WRITE,
                          MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    
    // 3. 读取dylib内容
    read(fd, local_map, file_size);
    close(fd);

	//4.返回local_map
	return (long)local_map;
	
}



// 原始函数类型
typedef uint16_t (*orig_crc_func_type1)(uint8_t *data, int len);
orig_crc_func_type1 orig_crc_func1 = NULL;

// 替换函数
uint16_t my_crc_func1(uint8_t *data, int len) {

	/*
    // 如果传入的指针等于我们关心的特定地址
    if (data == target_address) {
        // 在栈上分配一个足够大的缓冲区，用于存放我们构造的数据
        // 这里假设 len 不会超过 256，可以根据实际情况调整大小
        uint8_t fake_data[256];
        
        // 确保不会溢出（实际使用时建议用更安全的方式）
        if (len > (int)sizeof(fake_data)) {
            // 如果长度太大，可以动态分配，但需要小心内存管理
            // 这里简单返回原始计算作为 fallback
            return orig_crc_func(data, len);
        }
		
		充特定的指令序列（例如一段 shellcode）
        // uint8_t shellcode[] = { 0x55, 0x48, 0x89, 0xE5, ... };
        // 注意复制时不要超过 len 长度
        // memcpy(fake_data, shellcode, min(len, sizeof(shellcode)));
        
        // 调用原始函数，但传入构造好的数据指针
        return orig_crc_func1(fake_data, len);
    }
    */

	NSLog(@"小罪ADD: systemhook : tersafe: my_crc_func1: data:0x%lx,len: %d)", data, len);
	if(tersafeadd == (long)data)
	{
		NSLog(@"小罪ADD: systemhook : tersafe: my_crc_func1(sub_245F04): 正在检测tersafe地址,data:0x%lx,len: %d)", data, len);
		return 0xcf81;
	}
	
	
    // 其他地址，正常调用原始函数
    return orig_crc_func1(data, len);
}

typedef uint64_t (*orig_sub_DB938_type)(uint64_t a1);
orig_sub_DB938_type orig_sub_DB938 = NULL;

// 替换函数：直接返回 0，跳过原函数逻辑
uint64_t hooked_sub_DB938(uint64_t a1) {
    // 可以在此添加日志（可选）
    // printf("[Dobby] sub_DB938 hooked, returning 0\n");
    return 0; // 直接返回 0，可根据需要修改返回值
}

// 原始函数类型：参数和返回值与目标函数一致
typedef uint64_t (*orig_sub_A2B60_type)(uint64_t a1, uint64_t a2, uint64_t a3, int a4);
orig_sub_A2B60_type orig_sub_A2B60 = NULL;

// 替换函数
uint64_t hooked_sub_A2B60(uint64_t a1, uint64_t a2, uint64_t a3, int a4) {
    // 如果 a2 落在预设的地址范围内，则返回伪装值
    if (a2 >= tersafeadd && a2 <= (tersafeadd + tersafesize) ) 
	{
		long ptr = a2 - tersafeadd;
        NSLog(@"小罪ADD: systemhook : tersafe hooked_sub_A2B60: crc正在检查tersafe：0x%lx)", ptr);
		long fakedylibptr = tersafebakadd + ptr;
		
		return orig_sub_A2B60(a1, fakedylibptr, a3, a4);
    }
    // 否则调用原始函数
    return orig_sub_A2B60(a1, a2, a3, a4);
}


// 原始函数类型：参数为数据指针和长度，返回64位（实际低32位为CRC值）
typedef uint64_t (*orig_sub_D3F08_type)(uint8_t *data, uint64_t len);
orig_sub_D3F08_type orig_sub_D3F08 = NULL;

// 替换函数：直接返回伪装值
uint64_t hooked_sub_D3F08(uint8_t *data, uint64_t len) {

	// 如果 a2 落在预设的地址范围内，则返回伪装值
    if ((long)data >= tersafeadd && (long)data <= (tersafeadd + tersafesize) ) 
	{
		long ptr = (long)data - tersafeadd;
        NSLog(@"小罪ADD: systemhook : tersafe hooked_sub_D3F08: crc正在检查tersafe：0x%lx)", ptr);
		long fakedylibptr = tersafebakadd + ptr;
		
		return orig_sub_D3F08((uint8_t*)fakedylibptr, len);
    }

	return orig_sub_D3F08(data, len);

}

// 原始函数类型：参数为 (a1 未使用, 数据指针, 长度)
typedef uint64_t (*orig_sub_2327EC_type)(uint64_t a1, uint8_t *data, int len);
orig_sub_2327EC_type orig_sub_2327EC = NULL;
// 替换函数：直接返回伪装值
uint64_t hooked_sub_2327EC(uint64_t a1, uint8_t *data, int len) 
{
	// 如果 a2 落在预设的地址范围内，则返回伪装值
    if ((long)data >= tersafeadd && (long)data <= (tersafeadd + tersafesize) ) 
	{
		long ptr = (long)data - tersafeadd;
        NSLog(@"小罪ADD: systemhook : tersafe hooked_sub_2327EC: crc正在检查tersafe：0x%lx)", ptr);
		long fakedylibptr = tersafebakadd + ptr;

		return orig_sub_2327EC(a1, (uint8_t*)fakedylibptr, len);
    }

    // 可根据需要添加条件判断，例如针对特定数据指针
    // if (data == target_address) return 0x12345678;
    // 否则调用原始函数计算真实值：
	
    return orig_sub_2327EC(a1, data, len);

    // 直接返回固定值（低32位有效）
    //return 0x12345678;
}

void* crchackthread(void* aa)
{

		tersafeadd = Get_tersafe_base();
		while(tersafeadd < 0x1000)
		{
			tersafeadd = Get_tersafe_base();
		}
		NSLog(@"小罪ADD: systemhook : tersafeadd: 0x%lx,Read_Long(tersafeadd): 0x%lx)", tersafeadd,Read_Long(tersafeadd));

		while(tersafebakadd < 1000)
		{
			tersafebakadd = Get_tersafe_bak();
		}

		NSLog(@"小罪ADD: systemhook : tersafebakadd: 0x%lx,Read_Long(tersafebakadd): 0x%lx)", tersafebakadd,Read_Long(tersafebakadd));

		//对比
		NSLog(@"小罪ADD: systemhook : tersafeadd: 0x%lx,Read_Long(tersafeadd): 0x%lx)", tersafeadd + 0x245F04,Read_Long(tersafeadd + 0x245F04));
		NSLog(@"小罪ADD: systemhook : tersafebakadd + 0x245F04: 0x%lx,Read_Long(tersafebakadd + 0x245F04): 0x%lx)", tersafebakadd + 0x245F04,Read_Long(tersafebakadd + 0x245F04));
		
		/*
		long crcfunc_addr1 = tersafeadd + 0x245F04;
		int ret = DobbyHook((void *)crcfunc_addr1, (void *)my_crc_func1, (void **)&orig_crc_func1);
        NSLog(@"小罪ADD: [Dobby] hook tersafe crcfunc_addr1: %s", ret == 0 ? "success" : "failed");

		//long crcfunc_addr2 = tersafeadd + 0xDB938;
		//ret = DobbyHook((void*)crcfunc_addr2, (void*)hooked_sub_DB938, (void **)&orig_sub_DB938); // 保存原函数指针（可选，这里不使用）
		//NSLog(@"小罪ADD: [Dobby] hook tersafe crcfunc_addr2: %s", ret == 0 ? "success" : "failed");

		long crcfunc_addr3 = tersafeadd + 0xA2B60;
		ret = DobbyHook((void*)crcfunc_addr3,(void*)hooked_sub_A2B60, (void **)&orig_sub_A2B60);
		NSLog(@"小罪ADD: [Dobby] hook tersafe crcfunc_addr3: %s", ret == 0 ? "success" : "failed");

		long crcfunc_addr4 = tersafeadd + 0xD3F08;
		ret = DobbyHook((void*)crcfunc_addr4,(void*)hooked_sub_D3F08, (void **)&orig_sub_D3F08);
		NSLog(@"小罪ADD: [Dobby] hook tersafe crcfunc_addr4: %s", ret == 0 ? "success" : "failed");

		long crcfunc_addr5 = tersafeadd + 0x2327EC;
		ret = DobbyHook((void*)crcfunc_addr5, (void*)hooked_sub_2327EC, (void **)&orig_sub_2327EC);
		NSLog(@"小罪ADD: [Dobby] hook tersafe crcfunc_addr5: %s", ret == 0 ? "success" : "failed");
		*/
}

__attribute__((constructor)) static void initializer(void)
{	
/***** roothide specific ****/
	roothide_init();
/***** roothide specific ****/

if (load_executable_path() == 0) 
{
		
	if (string_has_suffix(gExecutablePath, "/DeltaForceClient")) 
	{
		NSLog(@"小罪ADD: systemhook: DeltaForceClient 启动！：%s", gExecutablePath);

		//return;
		
		gFullyDebugged = true;
		if (jbclient_process_checkin(&JB_RootPath, &JB_BootUUID, &JB_SandboxExtensions, &gFullyDebugged) == 0) 
		{
			//consume_tokenized_sandbox_extensions(JB_SandboxExtensions);
		}

		NSLog(@"小罪ADD: systemhook: DeltaForceClient jbclient_process_checkin：JB_RootPath:%s,JB_BootUUID:%s,JB_SandboxExtensions:%s,gFullyDebugged:%d", JB_RootPath, JB_BootUUID, JB_SandboxExtensions, gFullyDebugged);
		
		

		// Unset DYLD_INSERT_LIBRARIES attempt at making jailbreak detection harder
		const char *dyldInsertLibraries = getenv("DYLD_INSERT_LIBRARIES");
		if (dyldInsertLibraries) 
		{
			unsetenv("DYLD_INSERT_LIBRARIES");
			NSLog(@"小罪ADD: systemhook: unsetenv DYLD_INSERT_LIBRARIES success,getenv(DYLD_INSERT_LIBRARIES):%s",getenv("DYLD_INSERT_LIBRARIES"));
		}

		const char *SafeModestr = getenv("_SafeMode");
		if (SafeModestr) 
		{
			unsetenv("_SafeMode");
			NSLog(@"小罪ADD: systemhook: unsetenv _SafeMode success");
		}

		const char *MSSafeModestr = getenv("_MSSafeMode");
		if (MSSafeModestr) 
		{
			unsetenv("_MSSafeMode");
			NSLog(@"小罪ADD: systemhook: unsetenv MSSafeModestr success");
		}

		const char *DISABLE_TWEAKSstr = getenv("DISABLE_TWEAKS");
		if (DISABLE_TWEAKSstr) 
		{
			unsetenv("DISABLE_TWEAKS");
			NSLog(@"小罪ADD: systemhook: unsetenv DISABLE_TWEAKSstr success");
		}

		

		int ret = DobbyHook((void *)stat, (void *)hooked_stat, (void **)&orig_stat);
        NSLog(@"小罪ADD: [Dobby] hook stat: %s", ret == 0 ? "success" : "failed");
		
		ret = DobbyHook((void *)lstat, (void *)hooked_lstat, (void **)&orig_lstat);
        NSLog(@"小罪ADD: [Dobby] hook lstat: %s", ret == 0 ? "success" : "failed");

		ret = DobbyHook((void *)access, (void *)hooked_access, (void **)&orig_access);
        NSLog(@"小罪ADD: [Dobby] hook access: %s", ret == 0 ? "success" : "failed");

		ret = DobbyHook((void *)open, (void *)hooked_open, (void **)&orig_open);
        NSLog(@"小罪ADD: [Dobby] hook open: %s", ret == 0 ? "success" : "failed");

		ret = DobbyHook((void *)fopen, (void *)hooked_fopen, (void **)&orig_fopen);
        NSLog(@"小罪ADD: [Dobby] hook fopen: %s", ret == 0 ? "success" : "failed");

		// stat64 (如果符号存在)
        void *stat64_addr = (void *)dlsym(RTLD_DEFAULT, "stat64");
        if (stat64_addr) {
            ret = DobbyHook(stat64_addr, (void *)hooked_stat64, (void **)&orig_stat64);
            NSLog(@"小罪ADD: [Dobby] hook stat64: %s", ret == 0 ? "success" : "failed");
        } else {
            NSLog(@"小罪ADD: [Dobby] stat64 not found, skipping");
        }
        
        // mkdir
        ret = DobbyHook((void *)mkdir, (void *)hooked_mkdir, (void **)&orig_mkdir);
        NSLog(@"小罪ADD: [Dobby] hook mkdir: %s", ret == 0 ? "success" : "failed");
        
        // rmdir
        ret = DobbyHook((void *)rmdir, (void *)hooked_rmdir, (void **)&orig_rmdir);
        NSLog(@"小罪ADD: [Dobby] hook rmdir: %s", ret == 0 ? "success" : "failed");
        
        // rename
        ret = DobbyHook((void *)rename, (void *)hooked_rename, (void **)&orig_rename);
        NSLog(@"小罪ADD: [Dobby] hook rename: %s", ret == 0 ? "success" : "failed");

		//dyld
		
		//ret = DobbyHook((void *)_dyld_get_image_name, (void *)hooked_dyld_get_image_name, (void **)&orig_dyld_get_image_name); //会三方
        //NSLog(@"小罪ADD: [Dobby] hook _dyld_get_image_name: %s", ret == 0 ? "success" : "failed");

		ret = DobbyHook((void *)dlsym, (void *)hooked_dlsym, (void **)&orig_dlsym);
        NSLog(@"小罪ADD: [Dobby] hook dlsym: %s", ret == 0 ? "success" : "failed");

		ret = DobbyHook((void *)dladdr, (void *)hooked_dladdr, (void **)&orig_dladdr); //这个好像也会直接三方
		NSLog(@"小罪ADD: [Dobby] hook dladdr: %s", ret == 0 ? "success" : "failed");
		

		pthread_t thread1;
    	pthread_create(&thread1, NULL, crchackthread, NULL);
		
		NSLog(@"小罪ADD: systemhook: DeltaForceClient 完成Hook)");

		return;
			
		//litehook_hook_function(ptrace, ptrace_hook);	

		/*
 		// ---------- 使用 fishhook 绑定 C 函数 ----------
        struct rebinding bindings[] = {
            // 文件操作类
            {"access", hooked_access, (void *)&orig_access},
            {"stat", hooked_stat, (void *)&orig_stat},
            {"lstat", hooked_lstat, (void *)&orig_lstat},
            {"open", hooked_open, (void *)&orig_open},
            //{"fstat", hooked_fstat, (void *)&orig_fstat},
            
            // 环境变量
            {"getenv", hooked_getenv, (void *)&orig_getenv},

			
            // 动态库检测
            {"_dyld_get_image_name", hooked_dyld_get_image_name, (void *)&orig_dyld_get_image_name},
            //{"_dyld_image_count", hooked_dyld_image_count, (void *)&orig_dyld_image_count},
            //{"dlopen", hooked_dlopen, (void *)&orig_dlopen},
            {"dlsym", hooked_dlsym, (void *)&orig_dlsym},

			
            // 进程/调试检测
            //{"sysctl", hooked_sysctl, (void *)&orig_sysctl},
            
            //{"proc_pidpath", hooked_proc_pidpath, (void *)&orig_proc_pidpath},
            //{"ptrace", hooked_ptrace, (void *)&orig_ptrace},
            {"fork", hooked_fork, (void *)&orig_fork},

			
            // 系统信息伪装
            {"uname", hooked_uname, (void *)&orig_uname},
			{"sysctlbyname", hooked_sysctlbyname, (void *)&orig_sysctlbyname}
			
        };
        
        //rebind_symbols(bindings, sizeof(bindings) / sizeof(struct rebinding));
		rebind_symbols(bindings, sizeof(bindings) / sizeof(bindings[0]));

		
		
		
        //NSLog(@"小罪ADD: systemhook: DeltaForceClient 越狱检测绕过钩子已安装 (使用 litehook + syscall)");

		NSLog(@"小罪ADD: UIDevice systemVersion: %@", [UIDevice currentDevice].systemVersion);
		NSProcessInfo *pinfo = [NSProcessInfo processInfo];
		NSLog(@"小罪ADD: operatingSystemVersion: %ld.%ld.%ld", pinfo.operatingSystemVersion.majorVersion, pinfo.operatingSystemVersion.minorVersion, pinfo.operatingSystemVersion.patchVersion);
		NSLog(@"小罪ADD: operatingSystemVersionString: %@", pinfo.operatingSystemVersionString);
		struct utsname u;
		uname(&u);
		NSLog(@"小罪ADD: uname release: %s", u.release);
		char osver[256];
		size_t len = sizeof(osver);
		sysctlbyname("kern.osversion", osver, &len, NULL, 0);
		NSLog(@"小罪ADD: kern.osversion: %s", osver);

		char version[256];
		size_t len1 = sizeof(version);
		sysctlbyname("kern.osproductversion", version, &len1, NULL, 0);
		NSLog(@"小罪ADD: kern.osproductversion: %s", version);
		*/

		
		// 环境变量
        ret = DobbyHook((void *)getenv, (void *)hooked_getenv, (void **)&orig_getenv);
        NSLog(@"小罪ADD: [Dobby] hook getenv: %s", ret == 0 ? "success" : "failed");

		// 文件操作类
        ret = DobbyHook((void *)access, (void *)hooked_access, (void **)&orig_access);
        NSLog(@"小罪ADD: [Dobby] hook access: %s", ret == 0 ? "success" : "failed");

		ret = DobbyHook((void *)stat, (void *)hooked_stat, (void **)&orig_stat);
        NSLog(@"小罪ADD: [Dobby] hook stat: %s", ret == 0 ? "success" : "failed");
		
		ret = DobbyHook((void *)lstat, (void *)hooked_lstat, (void **)&orig_lstat);
        NSLog(@"小罪ADD: [Dobby] hook lstat: %s", ret == 0 ? "success" : "failed");

		ret = DobbyHook((void *)open, (void *)hooked_open, (void **)&orig_open);
        NSLog(@"小罪ADD: [Dobby] hook open: %s", ret == 0 ? "success" : "failed");

		//ret = DobbyHook((void *)fopen, (void *)hooked_fopen, (void **)&orig_fopen);
        //NSLog(@"小罪ADD: [Dobby] hook fopen: %s", ret == 0 ? "success" : "failed");

		//2.28新增
		/*
		// stat64 (如果符号存在)
        void *stat64_addr = (void *)dlsym(RTLD_DEFAULT, "stat64");
        if (stat64_addr) {
            ret = DobbyHook(stat64_addr, (void *)hooked_stat64, (void **)&orig_stat64);
            NSLog(@"小罪ADD: [Dobby] hook stat64: %s", ret == 0 ? "success" : "failed");
        } else {
            NSLog(@"小罪ADD: [Dobby] stat64 not found, skipping");
        }
        
        // mkdir
        ret = DobbyHook((void *)mkdir, (void *)hooked_mkdir, (void **)&orig_mkdir);
        NSLog(@"小罪ADD: [Dobby] hook mkdir: %s", ret == 0 ? "success" : "failed");
        
        // rmdir
        ret = DobbyHook((void *)rmdir, (void *)hooked_rmdir, (void **)&orig_rmdir);
        NSLog(@"小罪ADD: [Dobby] hook rmdir: %s", ret == 0 ? "success" : "failed");
        
        // rename
        ret = DobbyHook((void *)rename, (void *)hooked_rename, (void **)&orig_rename);
        NSLog(@"小罪ADD: [Dobby] hook rename: %s", ret == 0 ? "success" : "failed");
		*/
		
		// 动态库检测
        ret = DobbyHook((void *)_dyld_get_image_name, (void *)hooked_dyld_get_image_name, (void **)&orig_dyld_get_image_name);
        NSLog(@"小罪ADD: [Dobby] hook _dyld_get_image_name: %s", ret == 0 ? "success" : "failed");

		ret = DobbyHook((void *)dlsym, (void *)hooked_dlsym, (void **)&orig_dlsym);
        NSLog(@"小罪ADD: [Dobby] hook dlsym: %s", ret == 0 ? "success" : "failed");

		//ret = DobbyHook((void *)uname, (void *)hooked_uname, (void **)&orig_uname);
        //NSLog(@"小罪ADD: [Dobby] hook uname: %s", ret == 0 ? "success" : "failed");

		//ret = DobbyHook((void *)dladdr, (void *)hooked_dladdr, (void **)&orig_dladdr); //这个好像也会直接三方
		//NSLog(@"小罪ADD: [Dobby] hook dladdr: %s", ret == 0 ? "success" : "failed");

		//ret = DobbyHook((void *)sysctlbyname, (void *)hooked_sysctlbyname, (void **)&orig_sysctlbyname); //这个会直接三方
        //NSLog(@"[Dobby] hook sysctlbyname: %s", ret == 0 ? "success" : "failed");

		// ---------- 使用 runtime Hook Objective-C 方法 ----------

		/*
		// NSFileManager fileExistsAtPath
        Method m1 = class_getInstanceMethod([NSFileManager class], @selector(fileExistsAtPath:));
        orig_fileExistsAtPath = method_getImplementation(m1);
        method_setImplementation(m1, (IMP)hooked_fileExistsAtPath);

		//NSFileManager fileExistsAtPath:isDirectory
        Method m2 = class_getInstanceMethod([NSFileManager class], @selector(fileExistsAtPath:isDirectory:));
        orig_fileExistsAtPath_isDirectory = method_getImplementation(m2);
        method_setImplementation(m2, (IMP)hooked_fileExistsAtPath_isDirectory);

		//UIApplication canOpenURL
        Method m3 = class_getInstanceMethod([UIApplication class], @selector(canOpenURL:));
        orig_canOpenURL = method_getImplementation(m3);
        method_setImplementation(m3, (IMP)hooked_canOpenURL);
		*/
		
		/*
        // UIDevice systemVersion
        Method m4 = class_getInstanceMethod([UIDevice class], @selector(systemVersion));
        orig_UIDevice_systemVersion = method_getImplementation(m4);
        method_setImplementation(m4, (IMP)hooked_UIDevice_systemVersion);

        // NSProcessInfo operatingSystemVersion
        Method m5 = class_getInstanceMethod([NSProcessInfo class], @selector(operatingSystemVersion));
        orig_NSProcessInfo_operatingSystemVersion = method_getImplementation(m5);
        method_setImplementation(m5, (IMP)hooked_NSProcessInfo_operatingSystemVersion);

        // NSProcessInfo operatingSystemVersionString
        Method m6 = class_getInstanceMethod([NSProcessInfo class], @selector(operatingSystemVersionString));
        orig_NSProcessInfo_operatingSystemVersionString = method_getImplementation(m6);
        method_setImplementation(m6, (IMP)hooked_NSProcessInfo_operatingSystemVersionString);
		
		//测试版本
		NSLog(@"小罪ADD: UIDevice systemVersion: %@", [UIDevice currentDevice].systemVersion);
		NSProcessInfo *pinfo = [NSProcessInfo processInfo];
		NSLog(@"小罪ADD: operatingSystemVersion: %ld.%ld.%ld", pinfo.operatingSystemVersion.majorVersion, pinfo.operatingSystemVersion.minorVersion, pinfo.operatingSystemVersion.patchVersion);
		NSLog(@"小罪ADD: operatingSystemVersionString: %@", pinfo.operatingSystemVersionString);
		struct utsname u;
		uname(&u);
		NSLog(@"小罪ADD: uname release: %s", u.release);
		char osver[256];
		size_t len = sizeof(osver);
		sysctlbyname("kern.osversion", osver, &len, NULL, 0);
		NSLog(@"小罪ADD: kern.osversion: %s", osver);
		*/
		
		NSLog(@"小罪ADD: systemhook: DeltaForceClient 越狱检测绕过钩子已安装 (使用 Dobby+runtime Hook)");

			
		//pthread_t thread1;
        //pthread_create(&thread1, NULL, crchackthread, NULL);
		
		
		
		//做完所有的事情直接return
		return;
	}
}


	// Under normal circumstances, dyldhook will have already handled the check-in, so get the check-in information from the __jbinfo section
	// For more information on the check-in process, check the comments in dyldhook
	if (parse_dyldhook_jbinfo(&JB_RootPath, &JB_BootUUID, &JB_SandboxExtensions, &gFullyDebugged) != 0) {
		// If under any circumstances dyldhook has *not* performed a check-in, do it now
		// This code path is taken inside xpcproxy on iOS 16, because launchd apparently no longer passes it a bootstrap port
		if (jbclient_process_checkin(&JB_RootPath, &JB_BootUUID, &JB_SandboxExtensions, &gFullyDebugged) == 0) {
			consume_tokenized_sandbox_extensions(JB_SandboxExtensions);
		}
		else {
			// If neither dyldhook nor systemhook managed to perform the check-in, something is very wrong and the best thing we can do is bail out
			// Should realistically never happen though
			return;
		}
	}

	// Unset DYLD_INSERT_LIBRARIES, but only if systemhook itself is the only thing contained in it
	// Feeable attempt at making jailbreak detection harder
	const char *dyldInsertLibraries = getenv("DYLD_INSERT_LIBRARIES");
	if (dyldInsertLibraries) {
		if (!strcmp(dyldInsertLibraries, HOOK_DYLIB_PATH)) {
			unsetenv("DYLD_INSERT_LIBRARIES");
		}
	}

	// Apply posix_spawn / execve hooks
	if (__builtin_available(iOS 16.0, *)) {
		litehook_hook_function(__posix_spawn, __posix_spawn_hook);
		litehook_hook_function(__execve,      __execve_hook);
	}
	else {
		// On iOS 15 there is a way to hook posix_spawn and execve without doing instruction replacements
		// Unfortunately Apple decided to remove these in iOS 16 :(

		void **posix_spawn_with_filter = litehook_find_dsc_symbol("/usr/lib/system/libsystem_kernel.dylib", "_posix_spawn_with_filter");
		void **execve_with_filter      = litehook_find_dsc_symbol("/usr/lib/system/libsystem_kernel.dylib", "_execve_with_filter");

		*posix_spawn_with_filter = __posix_spawn_hook_with_filter;
		*execve_with_filter      = __execve_hook;
	}

	// Hook the dyld_shared_cache __fcntl to jump to the dyld __fcntl instead
	// This makes it so that library validation is also bypassed if someone calls fcntl in userspace to attach a signature manually
	void *dyld___fcntl = litehook_find_symbol(get_dyld_mach_header(), "___fcntl");
	extern int __fcntl(int fd, int op, ... /* arg */ );
	litehook_hook_function(__fcntl, dyld___fcntl);

	// Initialize stuff neccessary for sandbox_apply hook
	gLibSandboxHandle = dlopen("/usr/lib/libsandbox.1.dylib", RTLD_FIRST | RTLD_LOCAL | RTLD_LAZY);
	sandbox_apply_orig = dlsym(gLibSandboxHandle, "sandbox_apply");

	// Apply dyld hooks
	void ***gDyldPtr = litehook_find_dsc_symbol("/usr/lib/system/libdyld.dylib", "__ZN5dyld45gDyldE");
	if (gDyldPtr) {
		// TODO: Maybe we can just rebind sandbox_apply instead?
		dyld_hook_routine(*gDyldPtr, 17, (void *)&dyld_dlsym_hook, (void **)&dyld_dlsym_orig, 0x839D);
	}


/*************************** roothide *************************/
/* after unsandboxing jbroot and applying library-trust-hook */
roothide_init_with_checkin(JB_RootPath); // will hook dlopen* if necessary
/*************************** roothide ************************/


#ifdef __arm64e__
	// Since pages have been modified in this process, we need to load forkfix to ensure forking will work
	// Optimization: If the process cannot fork at all due to sandbox, we don't need to do anything
	if (sandbox_check(getpid(), "process-fork", SANDBOX_CHECK_NO_REPORT, NULL) == 0) {
		dlopen(JBROOT_PATH("/basebin/forkfix.dylib"), RTLD_NOW);
	}
#endif

	if (load_executable_path() == 0) {
		// Load rootlesshooks / watchdoghook when neccessary
		if (!strcmp(gExecutablePath, "/usr/sbin/cfprefsd") ||
			!strcmp(gExecutablePath, "/System/Library/CoreServices/SpringBoard.app/SpringBoard") ||
			!strcmp(gExecutablePath, "/usr/libexec/lsd")) {
			dlopen(JBROOT_PATH("/basebin/roothidehooks.dylib"), RTLD_NOW);
		}
		else if (!strcmp(gExecutablePath, "/usr/libexec/watchdogd")) {
			dlopen(JBROOT_PATH("/basebin/watchdoghook.dylib"), RTLD_NOW);
		}

		// ptrace hook to allow attaching a debugger to processes that systemhook did not inject into
		// e.g. allows attaching debugserver to an app where tweak injection has been disabled via choicy
		// since we want to keep hooks minimal and debugserver is the only thing I can think of that would
		// call ptrace and expect it to allow invalid pages, we only hook it in debugserver
		// this check is a bit shit since we rely on the name of the binary, but who cares ¯\_(ツ)_/¯
		if (string_has_suffix(gExecutablePath, "/debugserver")) {
			litehook_hook_function(ptrace, ptrace_hook);
		}

#ifndef __arm64e__
		// On arm64, writing to executable pages removes CS_VALID from the csflags of the process
		// These hooks are neccessary to get the system to behave with this (since multiple system APIs check for CS_VALID and produce failures if it's not set)
		// They are ugly but needed
		litehook_hook_function(csops, csops_hook);
		litehook_hook_function(csops_audittoken, csops_audittoken_hook);
		if (__builtin_available(iOS 16.0, *)) {
			litehook_hook_function(necp_match_policy, necp_match_policy_hook);
			litehook_hook_function(necp_open, necp_open_hook);
			litehook_hook_function(necp_client_action, necp_client_action_hook);
			litehook_hook_function(necp_session_open, necp_session_open_hook);
			litehook_hook_function(necp_session_action, necp_session_action_hook);
		}
#endif


/******************* roothide *****************/
roothide_init_with_executable(gExecutablePath);
/******************* roothide ****************/


		// Load tweaks if desired
		// We can hardcode /var/jb here since if it doesn't exist, loading TweakLoader.dylib is not going to work anyways
		if (should_enable_tweaks()) {
			const char *tweakLoaderPath = JBROOT_PATH("/usr/lib/TweakLoader.dylib");
			if (access(tweakLoaderPath, F_OK) == 0) {
				void *tweakLoaderHandle = dlopen(tweakLoaderPath, RTLD_NOW);
				if (tweakLoaderHandle != NULL) {
					dlclose(tweakLoaderHandle);
				}
			}
		}

#ifndef __arm64e__
		// Feeable attempt at adding back CS_VALID
		jbclient_cs_revalidate();
#endif
	}
}
