#include "common.h"
#include "roothider.h"

#import <Foundation/Foundation.h>
//#import <Metal/Metal.h>

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

#import <mach/mach.h>
#include <sys/mman.h>

#import <mach/vm_region.h>
#import <unistd.h>

#include "MemoryShare.h"

#include <mach-o/dyld.h>
#include <mach-o/loader.h>

#include <objc/message.h>
#include <UIKit/UIKit.h>
#include <dispatch/dispatch.h>

ShareStruct *shareData = 0;
kfdShareStruct *kfdshareData= 0;

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
long selfdylibheadersize = 0xB68;

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


extern  kern_return_t mach_vm_protect
(
 vm_map_t target_task,
 mach_vm_address_t address,
 mach_vm_size_t size,
 boolean_t set_maximum,
 vm_prot_t new_protection
 );
extern  kern_return_t
mach_vm_region_recurse(
                       vm_map_t                 map,
                       mach_vm_address_t        *address,
                       mach_vm_size_t           *size,
                       uint32_t                 *depth,
                       vm_region_recurse_info_t info,
                       mach_msg_type_number_t   *infoCnt);

extern  kern_return_t
mach_vm_read_overwrite(
                       vm_map_t           target_task,
                       mach_vm_address_t  address,
                       mach_vm_size_t     size,
                       mach_vm_address_t  data,
                       mach_vm_size_t     *outsize);

extern  kern_return_t
mach_vm_write(
              vm_map_t                          map,
              mach_vm_address_t                 address,
              pointer_t                         data,
              __unused mach_msg_type_number_t   size);




extern  kern_return_t
mach_vm_region
(
    mach_port_t target_task,
    mach_vm_address_t *address,
    mach_vm_size_t *size,
    vm_region_flavor_t flavor,
    vm_region_info_t info,
    mach_msg_type_number_t *infoCnt,
    mach_port_t *object_name
);
 
extern  kern_return_t mach_vm_allocate
(
    vm_map_t target,
    mach_vm_address_t *address,
    mach_vm_size_t size,
    int flags
);

extern  kern_return_t mach_vm_deallocate(vm_map_t target, mach_vm_address_t address, mach_vm_size_t size);

extern  kern_return_t mach_vm_remap
 (
  vm_map_t dst, mach_vm_address_t *dst_addr, mach_vm_size_t size, mach_vm_offset_t mask, int flags, vm_map_t src, mach_vm_address_t src_addr, boolean_t copy, vm_prot_t *cur_prot, vm_prot_t *max_prot, vm_inherit_t inherit
  );

extern  kern_return_t
mach_vm_region_recurse(
                       vm_map_t                 map,
                       mach_vm_address_t        *address,
                       mach_vm_size_t           *size,
                       uint32_t                 *depth,
                       vm_region_recurse_info_t info,
                       mach_msg_type_number_t   *infoCnt);

extern  kern_return_t
mach_vm_read_overwrite(
                       vm_map_t           target_task,
                       mach_vm_address_t  address,
                       mach_vm_size_t     size,
                       mach_vm_address_t  data,
                       mach_vm_size_t     *outsize);

extern  kern_return_t mach_vm_read(vm_map_t target_task, mach_vm_address_t address, mach_vm_size_t size, vm_offset_t *data, mach_msg_type_number_t *dataCnt);


extern 
kern_return_t mach_vm_page_query(vm_map_read_t target_map, mach_vm_offset_t offset, integer_t *disposition, integer_t *ref_count);


bool 是否缺页(long address)
{
	

    //内存属性
    
    
    mach_port_t object_name;
    mach_vm_size_t region_size=0;
    mach_vm_address_t region_base = (uint64_t)address;
    
    vm_region_basic_info_data_64_t info = {0};
    mach_msg_type_number_t info_cnt = VM_REGION_BASIC_INFO_COUNT_64;
    
    
    kern_return_t kr = mach_vm_region(mach_task_self(), &region_base, &region_size,
                                      VM_REGION_BASIC_INFO_64, (vm_region_info_t)&info, &info_cnt, &object_name);
    if(kr != KERN_SUCCESS) {
        //NSLog(@"mach_vm_region failed! %p", region_base);
        return true;
    }

    long addbase = (long)address & ~(PAGE_SIZE-1);
    long juliptr = address - addbase ;
    
    int pqueryinfo;
    kern_return_t    ret;
    pqueryinfo = 0;
    int numref;
    int mincoreinfo=0;
    
    ret = mach_vm_page_query(mach_task_self(), addbase, &pqueryinfo, &numref);
    
    if (ret != KERN_SUCCESS)
    {
        pqueryinfo = 0;
        //NSLog(@"小罪add : mach_vm_page_query call fail !");
    }
    
    /*
    if (pqueryinfo & VM_PAGE_QUERY_PAGE_PRESENT) mincoreinfo |= MINCORE_INCORE;
    if (pqueryinfo & VM_PAGE_QUERY_PAGE_REF)     mincoreinfo |= MINCORE_REFERENCED;
    if (pqueryinfo & VM_PAGE_QUERY_PAGE_DIRTY)   mincoreinfo |= MINCORE_MODIFIED;
    */
    if (pqueryinfo & VM_PAGE_QUERY_PAGE_PRESENT)
    {
        mincoreinfo |= MINCORE_INCORE;
     }
     if (pqueryinfo & VM_PAGE_QUERY_PAGE_REF)
     {
        mincoreinfo |= MINCORE_REFERENCED;
    }
    if (pqueryinfo & VM_PAGE_QUERY_PAGE_DIRTY)
    {
        mincoreinfo |= MINCORE_MODIFIED;
    }
    if (pqueryinfo & VM_PAGE_QUERY_PAGE_PAGED_OUT)
    {
        mincoreinfo |= MINCORE_PAGED_OUT;
    }
    if (pqueryinfo & VM_PAGE_QUERY_PAGE_COPIED)
    {
        mincoreinfo |= MINCORE_COPIED;
    }
    if ((pqueryinfo & VM_PAGE_QUERY_PAGE_EXTERNAL) == 0)
    {
        mincoreinfo |= MINCORE_ANONYMOUS;
    }
    //NSLog(@"小罪add : pqueryinfo:%d numref:%d mincoreinfo:%d",pqueryinfo,numref,mincoreinfo);
    
    if(pqueryinfo == 0 || numref == 0 || mincoreinfo == 0)
    {
        //NSLog(@"小罪add : 缺页地址:%lx",addbase);
        
        return true;
    }
        
    
    
    
    /*
    vm_prot_t cur_prot=0,  max_prot=0;
     
    kr = mach_vm_remap (mach_task_self(), (mach_vm_address_t *)&selfpage, PAGE_SIZE, 0, VM_FLAGS_FIXED | VM_FLAGS_OVERWRITE, task, (mach_vm_address_t)addbase,false, &cur_prot, &max_prot, VM_INHERIT_NONE);

    //kern_return_t kr = mach_vm_remap (mach_task_self(), (mach_vm_address_t *)&shijuaddbase, PAGE_SIZE, 0, VM_FLAGS_ANYWHERE, task, (mach_vm_address_t)new_page,true, &cur_prot, &max_prot, VM_INHERIT_SHARE);

    if (kr != KERN_SUCCESS) {
        
        
        NSLog(@"小罪add remap failed");
        return false;

        //NSLog(@"小罪add remap failed");
        // 处理错误
        //jinggao(@"remap failed");
    }
    else{
        NSLog(@"小罪add remap success");
    }
    */
    

    /*
    getchar();
    
    //char* state = NULL;

    //unsigned char state;
    
    //unsigned char *state = (unsigned char *)malloc(1);
    
    unsigned char vec = 0;
    
    //mincore(<#const void *#>, size_t, <#char *#>)
    int jieguo = mincore((void *)addbase,PAGE_SIZE,(char *)&vec);
    
    if(jieguo != -1)
    {
        NSLog(@"小罪add jieguo:%d , state:%d ?",jieguo,vec);
        
        
        NSLog(@"小罪add 是否incore： %d",vec);
        
        //NSLog(@"小罪add 是否incore： %s",state ? "In core" : "Not in core");
        
        if(vec & 1)
        {
            NSLog(@"小罪add 内存页在物理中");
        }
        else
        {
            NSLog(@"小罪add 内存页不在物理中");
        }
 
        //free(state);
        
        long testimageadd = Read_Longself(selfpage+juliptr);
        
        NSLog(@"小罪add testimageadd :%lx",testimageadd);
        
    }
    else
    {
        NSLog(@"小罪add mincore fail");
        //return false;
    }
    */
    //vm_inherit
    
    return false;
}


BOOL isValidAddress (uintptr_t address)
{
    return address && address > 0x100000000 && address < 0xFFFFFFFFF;
}

void Read_Datanew(long Src,int Size,void* Dst)
{
	if (!isValidAddress(Src) ){
        return ;
    }

	if(是否缺页(Src) == true)
    {
         return ;
    }
	
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

int Read_Int(long src)
{
    int Buff=0;
    //Buff = read<int>(src);
    Read_Datanew(src,4,&Buff);
    return Buff;
}

short Read_Short(long src)
{
    short Buff=0;
    //Buff = read<unsigned short int>(src);
    Read_Datanew(src,2,&Buff);
    return Buff;
}

unichar Read_unichar(long src)
{
    unichar Buff=0;
    //Buff = read<unsigned short int>(src);
    Read_Datanew(src,sizeof(unichar),&Buff);
    return Buff;
}


float Read_Float(long src)
{
    float Buff=0;
    //Buff = read<float>(src);
    Read_Datanew(src,4,&Buff);
    return Buff;
}

char Read_Char(long src)
{
    char Buff=0;
    //Buff = read<float>(src);
    Read_Datanew(src,1,&Buff);
    return Buff;
}

void forcewritenew(mach_vm_address_t addres,int data)
{
 
    int size = 4;
    
    
    mach_port_t object_name;
    mach_vm_size_t region_size=0;
    mach_vm_address_t region_base = (uint64_t)addres;
    
    vm_region_basic_info_data_64_t info = {0};
    mach_msg_type_number_t info_cnt = VM_REGION_BASIC_INFO_COUNT_64;
    kern_return_t kr = mach_vm_region(mach_task_self(), &region_base, &region_size,
                                      VM_REGION_BASIC_INFO_64, (vm_region_info_t)&info, &info_cnt, &object_name);
    if(kr != KERN_SUCCESS) {
        NSLog(@"mach_vm_region failed! %p", region_base);
        return ;
    }
    
    
    vm_address_t base = 0;
    if(!(info.protection & VM_PROT_WRITE)) {
        //NSLog(@"unwritable region %p %x : %x", region_base, region_size, info.protection);
        base = (uint64_t)addres & ~PAGE_MASK;
        //c1越狱这里可能失败, 不能同时rwx??? c1这里返回成功但是实际上并没有成功!!!!
        //kr = mynewmach_vm_protect(task, base, PAGE_SIZE, false, info.protection|VM_PROT_WRITE|VM_PROT_COPY);
        kr = mach_vm_protect(mach_task_self(), base, PAGE_SIZE, false, info.protection|VM_PROT_WRITE|VM_PROT_COPY);
        if(kr != KERN_SUCCESS) {
            //NSLog(@"vm_protect failed! kr=%d [%p %x] : %x", kr, base, PAGE_SIZE, info.protection);
            
            //kr = mynewmach_vm_protect(task, base, PAGE_SIZE, false, VM_PROT_READ|VM_PROT_WRITE|VM_PROT_COPY);
            kr = mach_vm_protect(mach_task_self(), base, PAGE_SIZE, false, VM_PROT_READ|VM_PROT_WRITE|VM_PROT_COPY);
            if(kr != KERN_SUCCESS) {
                //NSLog(@"vm_protect failed2! kr=%d [%p %x] : %x", kr, base, PAGE_SIZE, info.protection);
                
                //NSLog(@"mprotect=%d, %d, %s", mprotect((void*)base, PAGE_SIZE, info.protection|VM_PROT_WRITE), errno, strerror(errno));
                
                return ;
            }
        }
    }
    
    //kern_return_t error = mynewmach_vm_write(task, addres, (vm_address_t)&data, size);
    kern_return_t error = mach_vm_write(mach_task_self(), addres, (vm_address_t)&data, size);
    if(error != KERN_SUCCESS && base)
    {
        //kr = mynewmach_vm_protect(task, base, PAGE_SIZE, false, VM_PROT_READ|VM_PROT_WRITE|VM_PROT_COPY);
        kr = mach_vm_protect(mach_task_self(), base, PAGE_SIZE, false, VM_PROT_READ|VM_PROT_WRITE|VM_PROT_COPY);
        
        if(kr != KERN_SUCCESS) {
            //NSLog(@"vm_protect again failed! kr=%d [%p %x] : %x", kr, base, PAGE_SIZE, info.protection);
        } else {
            //error = mynewmach_vm_write(task, addres, (vm_address_t)&data, size);
            error = mach_vm_write(mach_task_self(), addres, (vm_address_t)&data, size);
        }
        
    }
    
    if(error == KERN_SUCCESS && base)
    {
        vm_protect(mach_task_self(), base, PAGE_SIZE, false, info.protection);
    }
    
    //vm_protect(mach_task_self(), addres, size, NO, VM_PROT_READ | VM_PROT_WRITE|VM_PROT_COPY);
    //vm_write(mach_task_self(),addres,(vm_address_t)&data,size);
    //vm_protect(mach_task_self(), addres, size, NO, VM_PROT_READ |VM_PROT_EXECUTE);
    
    //kr = mynewmach_vm_protect(task, addres, PAGE_SIZE, false, VM_PROT_READ|VM_PROT_WRITE|VM_PROT_COPY);
    //kern_return_t kr = mach_vm_protect(task, addres, PAGE_SIZE, false, VM_PROT_READ|VM_PROT_WRITE|VM_PROT_COPY);
    //kern_return_t error = mach_vm_write(task, addres, (vm_address_t)&data, size);
    //kern_return_t error = mynewmach_vm_write(task, addres, (vm_address_t)&data, size);
    //kr = mynewmach_vm_protect(task, addres, PAGE_SIZE, false, VM_PROT_READ |VM_PROT_EXECUTE);
    //kr = mach_vm_protect(task, addres, PAGE_SIZE, false, VM_PROT_READ |VM_PROT_EXECUTE);
}

long Imageaddress = 0;

static long Get_Imageaddress_base() {
    uint32_t count = _dyld_image_count();
    for (int i = 0; i < count; i++) {
        const char * path = (const char *)_dyld_get_image_name(i);
        
        NSString *res = [NSString stringWithUTF8String:path];
        
        long linshiptr = (long)_dyld_get_image_vmaddr_slide(i);
        
        if([res hasSuffix:@"DeltaForceClient.app/DeltaForceClient"])// && linshiptr < 0x100000000
        {
            //continue;
            return linshiptr + 0x100000000;
        }
    }
    return 0;
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
		
		/*
		long hashptr = tersafeadd+0x133124;

		NSLog(@"小罪ADD: systemhook : hashptr开启前 Read_Int(hashptr) :0x%x,,hashptr::0x%lx",Read_Int(hashptr),hashptr);
		forcewritenew(hashptr, CFSwapInt32(0xC0035FD6));
		NSLog(@"小罪ADD: systemhook : hashptr修改成功 SUCCESS !Read_Int(hashptr) :0x%x,,hashptr::0x%lx",Read_Int(hashptr),hashptr);

		
		while(Imageaddress <  1000)
		{
		 	Imageaddress = Get_Imageaddress_base();
		}
		NSLog(@"小罪ADD: systemhook : Imageaddress: 0x%lx,Read_Long(Imageaddress): 0x%lx)", Imageaddress,Read_Long(Imageaddress));

		long wuhouadd = Imageaddress + 0x2F7228C;
		NSLog(@"小罪ADD: systemhook : 无后开启前 Read_Int(wuhouadd) :0x%x,,wuhouadd::0x%lx",Read_Int(wuhouadd),wuhouadd);
		forcewritenew(wuhouadd, CFSwapInt32(0xE003271E));
        forcewritenew(wuhouadd + 0xC, CFSwapInt32(0xE103271E));
		NSLog(@"小罪ADD: systemhook : 无后开启成功 SUCCESS !Read_Int(wuhouadd) :0x%x,,wuhouadd::0x%lx",Read_Int(wuhouadd),wuhouadd);
		*/
}

bool isAddressWritable(void *addr) {
    vm_address_t region_address = (vm_address_t)addr;
    vm_size_t region_size = 0;
    vm_region_basic_info_data_64_t info;
    mach_msg_type_number_t info_count = VM_REGION_BASIC_INFO_COUNT_64;
    memory_object_name_t object_name = 0;

    kern_return_t kr = vm_region_64(
        mach_task_self(),
        &region_address,
        &region_size,
        VM_REGION_BASIC_INFO_64,
        (vm_region_info_t)&info,
        &info_count,
        &object_name
    );

    if (kr != KERN_SUCCESS) {
        // 地址无效或未映射
        return false;
    }

    // 检查保护属性是否包含写权限
    return (info.protection & VM_PROT_WRITE) != 0;
}

bool setMemoryWritableAndClear(void *ptr, size_t size) {
    // 步骤1：获取页大小，用于对齐检查
    long pageSize = sysconf(_SC_PAGESIZE);
    
    // 步骤2：计算ptr所在区域的页起始地址和区域大小（需页对齐）
    void *pageStart = (void *)((uintptr_t)ptr & ~(pageSize - 1));
    size_t regionSize = ((uintptr_t)ptr + size + pageSize - 1) & ~(pageSize - 1);
    regionSize = regionSize - (uintptr_t)pageStart;
    
    // 步骤3：查询当前保护属性（可选，但有助于了解原始状态）
    vm_address_t region_address = (vm_address_t)pageStart;
    vm_size_t region_size = 0;
    vm_region_basic_info_data_64_t info;
    mach_msg_type_number_t info_count = VM_REGION_BASIC_INFO_COUNT_64;
    memory_object_name_t object_name = 0;
    
    kern_return_t kr = vm_region_64(
        mach_task_self(),
        &region_address,
        &region_size,
        VM_REGION_BASIC_INFO_64,
        (vm_region_info_t)&info,
        &info_count,
        &object_name
    );
    
    if (kr != KERN_SUCCESS) {
        // 地址无效或未映射，无法操作
        return false;
    }
    
    // 步骤4：检查当前是否可写，如果不可写，尝试修改
    BOOL originallyWritable = (info.protection & VM_PROT_WRITE) != 0;
    if (!originallyWritable) {
        // 尝试添加写权限
        if (mprotect(pageStart, regionSize, info.protection | PROT_WRITE) != 0) {
            // 修改失败，可能是权限不允许（例如代码段）
            return false;
        }
    }
    
    // 步骤5：执行 memset
    memset(ptr, 0, size);
    
    // 步骤6：如果原始权限不可写，且我们修改了权限，可以选择恢复
    if (!originallyWritable) {
        // 恢复原始保护属性
        //mprotect(pageStart, regionSize, info.protection);
    }
    
    return true;
}

BOOL vm_protect_and_clear(void *ptr, size_t size) {
    // 步骤1：获取当前任务端口
    mach_port_t task = mach_task_self();
    
    // 步骤2：先查询当前保护属性（用于后续恢复和验证）
    vm_address_t region_address = (vm_address_t)ptr;
    vm_size_t region_size = 0;
    vm_region_basic_info_data_64_t info;
    mach_msg_type_number_t info_count = VM_REGION_BASIC_INFO_COUNT_64;
    memory_object_name_t object_name = 0;
    
    kern_return_t kr = vm_region_64(
        task,
        &region_address,
        &region_size,
        VM_REGION_BASIC_INFO_64,
        (vm_region_info_t)&info,
        &info_count,
        &object_name
    );
    
    if (kr != KERN_SUCCESS) {
        NSLog(@"小罪ADD: vm_protect_and_clearvm_region 查询失败: %d", kr);
        return NO;
    }
    
    // 记录原始保护属性
    vm_prot_t original_prot = info.protection;
    BOOL originallyWritable = (original_prot & VM_PROT_WRITE) != 0;
    
    // 步骤3：如果不可写，尝试使用 vm_protect 添加写权限
    if (!originallyWritable) {
        // 设置 set_maximum = FALSE，仅修改当前权限
        kr = vm_protect(task, (vm_address_t)ptr, size, FALSE, 
                        original_prot | VM_PROT_WRITE);
        
        if (kr != KERN_SUCCESS) {
            NSLog(@"小罪ADD: vm_protect_and_clearvm_region vm_protect 添加写权限失败: %d (可能原因: 超过最大权限或地址无效)", kr);
            return NO;
        }
        
        // 步骤4：再次查询，验证权限是否真的修改成功
        vm_address_t verify_address = (vm_address_t)ptr;
        vm_size_t verify_size = 0;
        vm_region_basic_info_data_64_t verify_info;
        info_count = VM_REGION_BASIC_INFO_COUNT_64;
        
        kr = vm_region_64(
            task,
            &verify_address,
            &verify_size,
            VM_REGION_BASIC_INFO_64,
            (vm_region_info_t)&verify_info,
            &info_count,
            &object_name
        );
        
        if (kr == KERN_SUCCESS) {
            if ((verify_info.protection & VM_PROT_WRITE) == 0) {
                NSLog(@"小罪ADD: vm_protect_and_clearvm_region 警告：权限验证失败，仍然不可写");
                // 可以选择返回 NO 或继续，这里保守返回 NO
                return NO;
            }
        } else {
            NSLog(@"小罪ADD: vm_protect_and_clearvm_region 警告：无法验证权限修改结果");
        }
    }
    
    // 步骤5：执行 memset 写入操作
    memset(ptr, 0, size);
    
    // 步骤6：验证写入结果（可选但推荐）
    // 检查第一个字节是否确实被清零
    volatile uint8_t *bytes = (volatile uint8_t *)ptr;
    if (bytes[0] != 0) {  // 使用 volatile 防止编译器优化
        NSLog(@"小罪ADD: vm_protect_and_clearvm_region 警告：内存写入验证失败，数据未被清零");
        // 如果写入验证失败，可以选择是否恢复原始权限
    }
    
    // 步骤7：如果原始权限不可写，恢复原始保护属性
    if (!originallyWritable) {
        kr = vm_protect(task, (vm_address_t)ptr, size, FALSE, original_prot);
        if (kr != KERN_SUCCESS) {
            NSLog(@"小罪ADD: vm_protect_and_clearvm_region 恢复原始权限失败: %d", kr);
            // 即使恢复失败，写入操作已经完成，可根据需要处理
        }
    }
    
    return YES;
}

BOOL vm_write_clear(void *ptr, size_t size) {
    mach_port_t task = mach_task_self();
    
    // 步骤1：查询当前保护属性（可选，用于后续恢复）
    vm_address_t region_address = (vm_address_t)ptr;
    vm_size_t region_size = 0;
    vm_region_basic_info_data_64_t info;
    mach_msg_type_number_t info_count = VM_REGION_BASIC_INFO_COUNT_64;
    memory_object_name_t object_name = 0;
    
    kern_return_t kr = vm_region_64(
        task,
        &region_address,
        &region_size,
        VM_REGION_BASIC_INFO_64,
        (vm_region_info_t)&info,
        &info_count,
        &object_name
    );
    
    if (kr != KERN_SUCCESS) {
        NSLog(@"小罪ADD: vm_write_clear：vm_region 查询失败: %d", kr);
        return NO;
    }
    
    vm_prot_t original_prot = info.protection;
    BOOL originallyWritable = (original_prot & VM_PROT_WRITE) != 0;
    
    // 步骤2：如果不可写，尝试用 vm_protect 添加写权限
    if (!originallyWritable) {
        kr = vm_protect(task, (vm_address_t)ptr, size, FALSE,
                        original_prot | VM_PROT_WRITE);
        if (kr != KERN_SUCCESS) {
            NSLog(@"小罪ADD: vm_write_clear：vm_protect 添加写权限失败: %d", kr);
            return NO;
        }
    }
    
    // 步骤3：准备源数据缓冲区（全零）
    void *zero_buffer = malloc(size);
    if (!zero_buffer) {
        NSLog(@"小罪ADD: vm_write_clear：内存分配失败");
        // 若之前修改了权限，尝试恢复
        if (!originallyWritable) {
            vm_protect(task, (vm_address_t)ptr, size, FALSE, original_prot);
        }
        return NO;
    }
    memset(zero_buffer, 0, size);  // 清零源缓冲区
    
    // 步骤4：调用 vm_write 写入零数据
    kr = vm_write(task,
                  (vm_address_t)ptr,
                  (vm_offset_t)zero_buffer,
                  (mach_msg_type_number_t)size);
    
    // 释放源缓冲区
    free(zero_buffer);
    
    if (kr != KERN_SUCCESS) {
        NSLog(@"小罪ADD: vm_write_clear：vm_write 失败: %d", kr);
        // 写入失败，但仍需恢复权限（如果修改过）
        if (!originallyWritable) {
            vm_protect(task, (vm_address_t)ptr, size, FALSE, original_prot);
        }
        return NO;
    }
    
    // 步骤5：验证写入结果（可选）
    volatile uint8_t *bytes = (volatile uint8_t *)ptr;
    if (bytes[0] != 0) {  // 检查第一个字节
        NSLog(@"小罪ADD: vm_write_clear：警告：写入验证失败，数据可能未清零");
    }
    
    // 步骤6：如果原始权限不可写，恢复原始保护属性
    if (!originallyWritable) {
        kr = vm_protect(task, (vm_address_t)ptr, size, FALSE, original_prot);
        if (kr != KERN_SUCCESS) {
            NSLog(@"小罪ADD: vm_write_clear：恢复原始权限失败: %d", kr);
            // 即使恢复失败，写入已完成，可根据需要处理
        }
    }
    
    return YES;
}

static bool hadgongxiang = false,hadqidongxiancheng = false;

void gongxiangkaiqi()
{
    //shareData = (ShareStruct*)openShareChannel(".gdata");
    //memset(shareData, 0, sizeof(ShareStruct));
	
    //kfdshareData = (kfdShareStruct*)openShareChannel();
    //memset(kfdshareData, 0, sizeof(kfdShareStruct));

	//kfdshareData->huizhipid = getpid();
    //NSLog(@"小罪ADD: systemhook: kfdshareData->huizhipid :%d",kfdshareData->huizhipid);

	shareData = (ShareStruct*)openShareChannel();

    if(shareData == (void*)-1){
        NSLog(@"小罪ADD: systemhook: openShareChannel shareData fail");
        //kfdshareData = new kfdShareStruct();
		shareData = (struct ShareStruct*)malloc(sizeof(struct ShareStruct));
    }

	NSLog(@"小罪ADD: systemhook: openShareChannel get shareDataptr :0x%lx!",shareData);

	if(!isValidAddress((long)shareData))
	{
		NSLog(@"小罪ADD: systemhook: openShareChannel get shareDataptr fail!");
		return;
	}

	
    //memset(shareData, 0, sizeof(ShareStruct));
	//if(isAddressWritable((void*)shareData))
	if(vm_write_clear((void*)shareData,sizeof(struct ShareStruct)))
	{
    	NSLog(@"小罪ADD: systemhook: openShareChannel shareData success!");
	}
	else
	{
		NSLog(@"小罪ADD: systemhook: openShareChannel shareData fail!");
	}

	
	pid_t wholepid = getpid();
    shareData->pid = wholepid;
	NSLog(@"小罪ADD: systemhook: shareData->pid: %d",shareData->pid);

	NSLog(@"小罪ADD: systemhook: Imageaddress:%lx,Read_Long(Imageaddress):%lx",Imageaddress,Read_Long(Imageaddress));

	shareData->baseAddress = Imageaddress;
    shareData->readbaseAddress = Read_Long(Imageaddress);
        
    NSLog(@"小罪ADD: systemhook: shareData->baseAddress:%lx,shareData->readbaseAddress:%lx",shareData->baseAddress,shareData->readbaseAddress);
	

}

struct MinimalViewInfo MinimalViewInfo = {};
struct Rotation矩阵 Rotation矩阵= {};

struct 三角函数 {
    float 正弦;
    float 余弦;
};

struct MinimalViewInfo 获取MinimalViewInfo(long POV) {
    
    //struct MinimalViewInfo selfMinimalViewInfo = {};
	struct MinimalViewInfo selfMinimalViewInfo = {};
    
    selfMinimalViewInfo.Location.X = Read_Float(POV + 0x0);
    selfMinimalViewInfo.Location.Y = Read_Float(POV + 0x0 + 4);
    selfMinimalViewInfo.Location.Z = Read_Float(POV + 0x0 + 4 + 4);

    
    selfMinimalViewInfo.Rotation.Pitch  = Read_Float(POV + 0x10);
    selfMinimalViewInfo.Rotation.Yaw  = Read_Float(POV + 0x10 + 4);
    selfMinimalViewInfo.Rotation.Roll  = Read_Float(POV + 0x10 + 4 + 4);
    
    selfMinimalViewInfo.FOV =  Read_Float(POV + 0x1c);
    
    return selfMinimalViewInfo;

};

struct Rotation矩阵 获取Rotation矩阵(struct Rotator Rotation) {
    struct 三角函数 Pitch = {
        sinf(Rotation.Pitch * M_PI / 180.0f),
        cosf(Rotation.Pitch * M_PI / 180.0f),
    };
    struct 三角函数 Yaw = {
        sinf(Rotation.Yaw * M_PI / 180.0f),
        cosf(Rotation.Yaw * M_PI / 180.0f),
    };
    struct 三角函数 Roll = {
        sinf(Rotation.Roll * M_PI / 180.0f),
        cosf(Rotation.Roll * M_PI / 180.0f),
    };
    return (struct Rotation矩阵){
        Pitch.余弦 * Yaw.余弦,
        Pitch.余弦 * Yaw.正弦,
        Pitch.正弦,
        
        Pitch.正弦 * Yaw.余弦 * Roll.正弦 - Yaw.正弦 * Roll.余弦,
        Pitch.正弦 * Yaw.正弦 * Roll.正弦 + Yaw.余弦 * Roll.余弦,
        Pitch.余弦 * -Roll.正弦,
        
        -(Pitch.正弦 * Yaw.余弦 * Roll.余弦 + Yaw.正弦 * Roll.正弦),
        Yaw.余弦 * Roll.正弦 - Pitch.正弦 * Yaw.正弦 * Roll.余弦,
        Pitch.余弦 * Roll.余弦,
    };
};


struct TeamComp 获取TeamComp(long Actor) {
    long TeamComp = Read_Long(Actor + 0x1090);
    
    //struct UGPTeamComponent* TeamComp; // 0x1090(0x08)
    if (!isValidAddress(TeamComp)) return (struct TeamComp){-1, -1};
    return (struct TeamComp){
        Read_Int(TeamComp + 0x108),
        Read_Int(TeamComp + 0x10C),
    };
};

struct Vector 获取RelativeLocation(long Actor) {
    long RootComponent = Read_Long(Actor + 0x180);
    if (!isValidAddress(RootComponent)) return (struct Vector){-1.0f, -1.0f, -1.0f};

    
    struct Vector RelativeLocation;
    
    RelativeLocation.X = Read_Float(RootComponent+0x220);
    RelativeLocation.Y = Read_Float(RootComponent+0x224);
    RelativeLocation.Z = Read_Float(RootComponent+0x228);
    
    return RelativeLocation;
    
    //return Read<Vector>(RootComponent + SDK::Class_SceneComponent::RelativeLocation);
};

struct Vector 获取对象距离Vector(struct Vector RelativeLocation,struct Vector Location, float 比例值) {
    return (struct Vector){
        (RelativeLocation.X - Location.X) / 比例值,
        (RelativeLocation.Y - Location.Y) / 比例值,
        (RelativeLocation.Z - Location.Z) / 比例值,
    };
};

float 获取对象距离(struct Vector RelativeLocation,struct Vector Location, float 比例值) {
    struct Vector 对象距离Vector = 获取对象距离Vector(RelativeLocation, Location, 比例值);
    return ceilf(sqrtf(powf(对象距离Vector.X, 2.0f) + powf(对象距离Vector.Y, 2.0f) + powf(对象距离Vector.Z, 2.0f)));
};

struct Vector2 获取对象屏幕ImVec2(struct Vector RelativeLocation,struct MinimalViewInfo MinimalViewInfo,struct Rotation矩阵 Rotation矩阵,struct Vector2 屏幕中心ImVec2) {
    struct Vector 对象距离Vector = 获取对象距离Vector(RelativeLocation, MinimalViewInfo.Location, 1.0f);
    struct Vector 对象转换Vector = {
        对象距离Vector.X * Rotation矩阵._10 + 对象距离Vector.Y * Rotation矩阵._11 + 对象距离Vector.Z * Rotation矩阵._12,
        对象距离Vector.X * Rotation矩阵._20 + 对象距离Vector.Y * Rotation矩阵._21 + 对象距离Vector.Z * Rotation矩阵._22,
        对象距离Vector.X * Rotation矩阵._00 + 对象距离Vector.Y * Rotation矩阵._01 + 对象距离Vector.Z * Rotation矩阵._02,
    };
    if (对象转换Vector.Z < 1.0f) 对象转换Vector.Z = 1.0f;
    return (struct Vector2 ){
        屏幕中心ImVec2.x + 对象转换Vector.X * (屏幕中心ImVec2.x / tanf(MinimalViewInfo.FOV * M_PI / 360.0f)) / 对象转换Vector.Z,
        屏幕中心ImVec2.y - 对象转换Vector.Y * (屏幕中心ImVec2.x / tanf(MinimalViewInfo.FOV * M_PI / 360.0f)) / 对象转换Vector.Z,
    };
};

struct Vector4D 获取对象屏幕ImVec4(struct Vector RelativeLocation, struct MinimalViewInfo MinimalViewInfo, struct Rotation矩阵 Rotation矩阵, struct Vector2 屏幕中心ImVec2) {
    struct Vector 顶部RelativeLocation = {
        RelativeLocation.X,
        RelativeLocation.Y,
        RelativeLocation.Z + 88.0f,
    };
    struct Vector 底部RelativeLocation = {
        RelativeLocation.X,
        RelativeLocation.Y,
        RelativeLocation.Z - 88.0f,
    };
    struct Vector2 顶部对象屏幕ImVec2 = 获取对象屏幕ImVec2(顶部RelativeLocation, MinimalViewInfo, Rotation矩阵, 屏幕中心ImVec2);
    struct Vector2 底部对象屏幕ImVec2 = 获取对象屏幕ImVec2(底部RelativeLocation, MinimalViewInfo, Rotation矩阵, 屏幕中心ImVec2);
    return (struct Vector4D ){
        顶部对象屏幕ImVec2.x,
        顶部对象屏幕ImVec2.y,
        (底部对象屏幕ImVec2.y - 顶部对象屏幕ImVec2.y) / 2.0f,
        底部对象屏幕ImVec2.y - 顶部对象屏幕ImVec2.y,
    };
};

NSString* 获取PlayerNamePrivate(long PlayerNamePrivate) {
    //NSMutableString *名字字符 = [NSMutableString string];
    NSMutableString *名字字符 = [[NSMutableString alloc] init];

    
       for (int Index = 0; Index < 14; Index++) {
           //unichar 名字字符串 = Read<unichar>(PlayerNamePrivate + Index * 2);
		   unichar 名字字符串 = Read_unichar(PlayerNamePrivate + Index * 2);
           if (名字字符串 == 0) break;
           [名字字符 appendFormat:@"%C", (unichar)名字字符串];
       }
       return [名字字符 copy];
};

struct EquipedArmorInfoArray {
    int ArmorLevel;
    int 护甲ArmorLevel;
};

typedef enum EAttachPosition{
    Attach_None = 0, // 无附着位置
    Attach_EquipmentStart = 100, // 装备开始位置
    Attach_Helmet = 101, // 头盔
    Attach_Headset = 102, // 耳机
    Attach_ArmedForceBaseProp = 103, // 武装部队基础道具
    Attach_Armband = 104, // 臂章
    Attach_BreastPlate = 105, // 胸甲
    Attach_Glasses = 106, // 眼镜
    Attach_ChestHanging = 107, // 胸前挂件
    Attach_Bag = 108, // 背包
    Attach_SafeBox = 109, // 保险箱
    Attach_Shoe = 110, // 鞋子
    Attach_MainWeaponLeft = 111, // 主武器（左侧）
    Attach_MainWeaponRight = 112, // 主武器（右侧）
    Attach_MeleeWeapon = 113, // 近战武器
    Attach_PistolWeapon = 114, // 手枪
    Attach_SecondaryWeapon = 1111, // 次要武器
    Attach_ArmedForceProp1 = 115, // 武装部队道具1
    Attach_KeyChain = 116, // 钥匙链
    Attach_ArmedForceProp2 = 117, // 武装部队道具2
    Attach_Character = 118, // 角色
    Attach_DogTag = 119, // 狗牌
    PVEMainWeaponLeft = 120, // PVE主武器（左侧）
    PVEMainWeaponRight = 121, // PVE主武器（右侧）
    Medical = 122, // 医疗物品
    Archive = 123, // 档案
    Attach_SceneWeapon = 124, // 场景武器
    Attach_ClassMeleeEquipment = 125, // 职业近战装备
    Attach_ClassThrowableEquipment = 126, // 职业投掷装备
    Attach_ClassConsumable = 127, // 职业消耗品
    Attach_PVEWeapon = 128, // PVE武器
    Attach_MissionMeleeEquipment = 129, // 任务近战装备
    Attach_BulletLeft = 131, // 左侧子弹
    Attach_BulletRight = 132, // 右侧子弹
    Attach_SkillWeaponSpecial = 133, // 特殊技能武器
    Attach_SkillWeaponUltimate = 134, // 终极技能武器
    Attach_SkillWeaponActive = 135, // 主动技能武器
    Attach_SkillWeaponSupport = 136, // 支援技能武器
    Attach_SkillWeaponBattleFieldPropSkill = 137, // 战场道具技能
    Attach_SkillWeaponCustom2 = 138, // 自定义技能武器2
    Attach_SkillWeaponCustom3 = 139, // 自定义技能武器3
    Attach_MP_Begin = 140, // 多人模式开始
    Attach_MP_ArmedForceBaseProp = 141, // MP武装部队基础道具
    Attach_MP_ArmedForceTDMProp = 142, // MP武装部队团队死斗道具
    Attach_MP_MainWeapon = 143, // MP主武器
    Attach_MP_SecondaryWeapon = 144, // MP次要武器
    Attach_MP_MeleeWeapon = 145, // MP近战武器
    Attach_MP_ArmedForceProp1 = 146, // MP武装部队道具1
    Attach_MP_ArmedForceProp2 = 147, // MP武装部队道具2
    Attach_MP_End = 148, // 多人模式结束
    Attach_EquipmentEnd = 150, // 装备结束
    Attach_Fashion = 200, // 时装
    Attach_AllNearby = 301, // 附近所有物品
    Attach_PickupBox = 302, // 拾取箱
    Attach_LootTmp = 303, // 临时战利品
    Attach_TmpPerk = 304, // 临时增益
    Attach_DeadbodyLootBox = 305, // 尸体战利品箱
    Attach_AbilityVehicle = 306, // 能力载具
    Attach_ContainerStart = 100000, // 容器开始
    Attach_ChestHangingContainer = 107001, // 胸前挂件容器
    Attach_BagContainer = 108001, // 背包容器
    Attach_SafeBoxContainer = 109001, // 保险箱容器
    Attach_KeyChainContainer = 116001, // 钥匙链容器
    Attach_ArchiveContainer = 123001, // 档案容器
    Attach_Pocket = 199997, // 口袋
    Attach_BagSpaceContainer = 199998, // 背包空间容器
    Attach_ContainerEnd = 199999, // 容器结束
    Attach_CarrayItem = 200001, // 携带物品
    Attach_Temp = 77777, // 临时
    Attach_TempContainer = 77777001, // 临时容器
    Attach_Temp_FortificationHammer = 77777002, // 临时防御锤
    Attach_PVE_RPG = 99999999, // PVE火箭筒
    EAttachPosition_MAX = 100000000 // 最大值
} EAttachPosition;


#pragma pack(push, 1) // 强制1字节对齐，防止编译器自动对齐
struct FArmorInfo2
{
    bool Status; // [偏移量: 0x00 | 大小: 0x01]
    char Padding1[3]; // 填充字节，使 AttachPosition 对齐到 0x04
    EAttachPosition AttachPosition; // [偏移量: 0x04 | 大小: 0x04]
    float ArmorHP; // [偏移量: 0x08 | 大小: 0x04]
    float MaxArmorHP; // [偏移量: 0x0C | 大小: 0x04]
    char Padding2[56]; // 填充至 0x48
    int32_t ArmorLevel; // [偏移量: 0x48 | 大小: 0x04]
};
#pragma pack(pop)

// ScriptStruct DFMGameplay.EquipmentInfo
// Size: 0x30 (Inherited: 0x00)
struct FEquipmentInfo {
    uint64_t ItemID; // 0x00(0x08)
    uint64_t gid; // 0x08(0x08)
    float Health; // 0x10(0x04)
    float MaxHealth; // 0x14(0x04)
    float Durability; // 0x18(0x04)
    float MaxDurability; // 0x1c(0x04)
    float TotalEquipSeceonds; // 0x20(0x04)
    float LastEquipTimeSeconds; // 0x24(0x04)
    float TotalApplyDamage; // 0x28(0x04)
    char pad_2C[0x4]; // 0x2c(0x04)
};

struct FArmorInfo2 GetArmorInfo2(struct FEquipmentInfo EquipmentInfo) {
    struct FArmorInfo2 info = { 0 };
    if (EquipmentInfo.ItemID > 10000000 && EquipmentInfo.ItemID < 20000000000) {
        //std::string str = std::to_string(EquipmentInfo.ItemID);
        //char* p = (char*)str.c_str();
		char str[32];  // 足够存放任意整数（包括 64 位）的十进制表示
		snprintf(str, sizeof(str), "%lld", EquipmentInfo.ItemID);  // 若 ItemID 是 long long，则用 "%lld"
		char *p = str;
        int v1 = (p[1] - '0') * 100;
        int v2 = (p[2] - '0') * 10;
        int v3 = p[3] - '0';
        int level = p[7] - '0';
        info.ArmorLevel = level;
        info.AttachPosition = (EAttachPosition)(v1 + v2 + v3);
        info.Status = TRUE;
    }
    return info;
}

struct EquipedArmorInfoArray 获取EquipedArmorInfoArray(long Actor) {
    
    int Armorlevel = 0;
    int HelmetArmorlevel = 0;
    
    long CharacterEquipComponentCache = Read_Long(Actor + 0x2208);//EncryptedObjectProperty CharacterEquipComponentCache; // 0x2188(0x08)
    long EquipmentInfoArray = Read_Long(CharacterEquipComponentCache + 0x1d8);// struct TArray<struct FEquipmentInfo> EquipmentInfoArray; // 0x1d8(0x10)
    
    struct FEquipmentInfo EquipPawn;
    
    for (int i = 0; i < 6; i++) {
        @autoreleasepool {
            //readMemory(EquipmentInfoArray + i * sizeof(struct FEquipmentInfo), &EquipPawn, sizeof(struct FEquipmentInfo));
            Read_Datanew(EquipmentInfoArray + i * sizeof(struct FEquipmentInfo),sizeof(struct FEquipmentInfo),&EquipPawn);
            struct FArmorInfo2 fArmorInfo2 = GetArmorInfo2(EquipPawn);
            // NSLog(@"dh666 ArmorHealth %d",fArmorInfo2.AttachPosition);
            if (fArmorInfo2.AttachPosition == Attach_BreastPlate)
            {
                Armorlevel = fArmorInfo2.ArmorLevel;
                
            } else if (fArmorInfo2.AttachPosition == Attach_Helmet)
            {
                HelmetArmorlevel = fArmorInfo2.ArmorLevel;
            }
        }
    }
    
    return (struct EquipedArmorInfoArray){
        HelmetArmorlevel,
        Armorlevel
    };
    
    
    

    

    return (struct EquipedArmorInfoArray){
        -1,
        -1,
    };
    

    
    
};

struct D3DXMATRIX {
    float _11, _12, _13, _14;
    float _21, _22, _23, _24;
    float _31, _32, _33, _34;
    float _41, _42, _43, _44;
};

struct Vector4 {
    float x;
    float y;
    float z;
    float w;
};



struct FTransform {
    struct Vector4 rot;
    struct Vector3new translation;
    struct Vector3new scale;
};

// 将成员函数改为外部函数，接受结构体指针参数
struct D3DXMATRIX FTransform_ToMatrixWithScale(struct FTransform* transform) {
    struct D3DXMATRIX m;
    m._41 = transform->translation.X;
    m._42 = transform->translation.Y;
    m._43 = transform->translation.Z;

    float x2 = transform->rot.x + transform->rot.x;
    float y2 = transform->rot.y + transform->rot.y;
    float z2 = transform->rot.z + transform->rot.z;

    float xx2 = transform->rot.x * x2;
    float yy2 = transform->rot.y * y2;
    float zz2 = transform->rot.z * z2;
    m._11 = (1.0f - (yy2 + zz2)) * transform->scale.X;
    m._22 = (1.0f - (xx2 + zz2)) * transform->scale.Y;
    m._33 = (1.0f - (xx2 + yy2)) * transform->scale.Z;

    float yz2 = transform->rot.y * z2;
    float wx2 = transform->rot.w * x2;
    m._32 = (yz2 - wx2) * transform->scale.Z;
    m._23 = (yz2 + wx2) * transform->scale.Y;

    float xy2 = transform->rot.x * y2;
    float wz2 = transform->rot.w * z2;
    m._21 = (xy2 - wz2) * transform->scale.Y;
    m._12 = (xy2 + wz2) * transform->scale.X;

    float xz2 = transform->rot.x * z2;
    float wy2 = transform->rot.w * y2;
    m._31 = (xz2 + wy2) * transform->scale.Z;
    m._13 = (xz2 - wy2) * transform->scale.X;

    m._14 = 0.0f;
    m._24 = 0.0f;
    m._34 = 0.0f;
    m._44 = 1.0f;

    return m;
}

// 静态成员函数改为普通函数
struct D3DXMATRIX FTransform_MatrixMultiplication(struct D3DXMATRIX pM1, struct D3DXMATRIX pM2) {
    struct D3DXMATRIX pOut;
    pOut._11 = pM1._11 * pM2._11 + pM1._12 * pM2._21 + pM1._13 * pM2._31 + pM1._14 * pM2._41;
    pOut._12 = pM1._11 * pM2._12 + pM1._12 * pM2._22 + pM1._13 * pM2._32 + pM1._14 * pM2._42;
    pOut._13 = pM1._11 * pM2._13 + pM1._12 * pM2._23 + pM1._13 * pM2._33 + pM1._14 * pM2._43;
    pOut._14 = pM1._11 * pM2._14 + pM1._12 * pM2._24 + pM1._13 * pM2._34 + pM1._14 * pM2._44;
    pOut._21 = pM1._21 * pM2._11 + pM1._22 * pM2._21 + pM1._23 * pM2._31 + pM1._24 * pM2._41;
    pOut._22 = pM1._21 * pM2._12 + pM1._22 * pM2._22 + pM1._23 * pM2._32 + pM1._24 * pM2._42;
    pOut._23 = pM1._21 * pM2._13 + pM1._22 * pM2._23 + pM1._23 * pM2._33 + pM1._24 * pM2._43;
    pOut._24 = pM1._21 * pM2._14 + pM1._22 * pM2._24 + pM1._23 * pM2._34 + pM1._24 * pM2._44;
    pOut._31 = pM1._31 * pM2._11 + pM1._32 * pM2._21 + pM1._33 * pM2._31 + pM1._34 * pM2._41;
    pOut._32 = pM1._31 * pM2._12 + pM1._32 * pM2._22 + pM1._33 * pM2._32 + pM1._34 * pM2._42;
    pOut._33 = pM1._31 * pM2._13 + pM1._32 * pM2._23 + pM1._33 * pM2._33 + pM1._34 * pM2._43;
    pOut._34 = pM1._31 * pM2._14 + pM1._32 * pM2._24 + pM1._33 * pM2._34 + pM1._34 * pM2._44;
    pOut._41 = pM1._41 * pM2._11 + pM1._42 * pM2._21 + pM1._43 * pM2._31 + pM1._44 * pM2._41;
    pOut._42 = pM1._41 * pM2._12 + pM1._42 * pM2._22 + pM1._43 * pM2._32 + pM1._44 * pM2._42;
    pOut._43 = pM1._41 * pM2._13 + pM1._42 * pM2._23 + pM1._43 * pM2._33 + pM1._44 * pM2._43;
    pOut._44 = pM1._41 * pM2._14 + pM1._42 * pM2._24 + pM1._43 * pM2._34 + pM1._44 * pM2._44;

    return pOut;
}

struct Vector3new GetBoneFTransform(long Mesh, int Id)
{
    long BoneActor;
    Read_Datanew(Mesh + 0x718, sizeof(BoneActor), &BoneActor);

    struct FTransform lpFTransform;
    Read_Datanew(BoneActor + Id * 0x30, sizeof(struct FTransform), &lpFTransform);

    struct FTransform ComponentToWorld;
    Read_Datanew(Mesh + 0x210, sizeof(struct FTransform), &ComponentToWorld);

    struct D3DXMATRIX Matrix = FTransform_MatrixMultiplication(
        FTransform_ToMatrixWithScale(&lpFTransform),
        FTransform_ToMatrixWithScale(&ComponentToWorld)
    );

    struct Vector3new result = (struct Vector3new){ Matrix._41, Matrix._42, Matrix._43 };
    return result;
}



struct Vector2 GameCanvas;
#define kWidth  [UIScreen mainScreen].bounds.size.width
#define kHeight [UIScreen mainScreen].bounds.size.height

void xunhuanhuizhi()
{

	GameCanvas.x = kWidth;//io.DisplaySize.x; //kWidth;
    GameCanvas.y = kHeight;//io.DisplaySize.y; //kHeight
    if(GameCanvas.x < GameCanvas.y)
    {
        GameCanvas.x = kHeight;//io.DisplaySize.x; //kWidth;
        GameCanvas.y = kWidth;//io.DisplaySize.y; //kHeight
    }
	
	long gworld = Read_Long(Imageaddress + 0x13A7B818);
	long NetDriver = Read_Long(gworld+0x30);//struct UNetDriver* NetDriver; // 0x30(0x08)
    long ServerConnection = Read_Long(NetDriver +0x88);//struct UNetConnection* ServerConnection; // 0x88(0x08)
    long PlayerController = Read_Long(ServerConnection +0x30);//struct APlayerController* PlayerController; // 0x30(0x08)
    long PlayerCameraManager = Read_Long(PlayerController +0x408);//EncryptedObjectProperty PlayerCameraManager; // 0x408(0x08)

	MinimalViewInfo = 获取MinimalViewInfo(PlayerCameraManager + 0x1780 + 0x10);//struct FTViewTarget ViewTarget; // 0x1780(0x9e0)
	Rotation矩阵 = 获取Rotation矩阵(MinimalViewInfo.Rotation);

	shareData->MinimalViewInfo = MinimalViewInfo;
    shareData->Rotation矩阵 = Rotation矩阵;

	long Pawn = Read_Long(PlayerController + 0x3A0);//struct APawn* Pawn; // 0x3a0(0x08)
	shareData->Pawn = Pawn;

	//NSLog(@"小罪ADD: systemhook: shareData->Pawn:%lx",shareData->Pawn);

	if(Pawn < 1000) return;
	
	struct TeamComp myselfTeamComp = 获取TeamComp(Pawn);
	shareData->myInfo.TeamComp = myselfTeamComp;

	long CacheCurWeapon = Read_Long(Pawn + 0x1718);//struct AWeaponBase* CacheCurWeapon; // 0x16f0(0x08)
    
    long WeaponID =  Read_Long(CacheCurWeapon + 0x828);//uint64_t WeaponID; // 0x828(0x08)
	shareData->myInfo.WeaponID = WeaponID;
    
    long BlackBoard = Read_Long(Pawn + 0xFF0);//struct UGPBlackboardComponent* BlackBoard; // 0xfc8(0x08)
    
    int bIsFiring = Read_Int(BlackBoard + 0x55E);//char bIsFiring : 1; // 0x50e(0x01)
	shareData->myInfo.bIsFiring = bIsFiring;
    
    float tmpdis = 999.0f;
    long tmptarget = 0;
    float tmptargetd3ddis = 0;

	
	long PersistentLevel1 = Read_Long(gworld+0xF8);
	long 世界数组1 = Read_Long(PersistentLevel1+0x98);
    int 世界数量1 = Read_Int(PersistentLevel1+0xA0);

	shareData->actorListcount = (int)世界数量1;
	//NSLog(@"小罪ADD: systemhook: shareData->actorListcount:%d",shareData->actorListcount);

	long cankaoptr = 0;
	
	int calint = 0;

	for (int Index = 0; Index < 世界数量1; Index++)
    {
		//calint = calint + 1;
		calint = Index;
		long 对象指针 = Read_Long(世界数组1 + Index * 0x8);
       	if(!isValidAddress(对象指针))continue;

		if(!isValidAddress(cankaoptr))
		{
			cankaoptr = 对象指针;
		}

		//if(labs(cankaoptr - 对象指针) >= (long)0xA0000000) continue;

		
		long CharacterMovement = Read_Long(对象指针 + 0x3D8);
		float MaxWalkSpeed = Read_Float(CharacterMovement + 0x1DC);
		uint32_t GNameID = Read_Int(对象指针 + 0x1C);

		if(MaxWalkSpeed >= 400.0f && MaxWalkSpeed <= 1500.0f)
		{
			shareData->playerInfo[calint].objtype = 1;
			
			//NSLog(@"小罪ADD: systemhook: Index:%d,对象指针:%lx",Index,对象指针);

			//NSLog(@"小罪ADD: systemhook: 准备赋值对象指针:%lx的actived为false",Index);
			shareData->playerInfo[calint].actived = false;
			//NSLog(@"小罪ADD: systemhook: 赋值对象指针:%lx的actived为false完成！");
			
			shareData->playerInfo[calint].GNameID = GNameID;

			struct TeamComp targetTeamComp = 获取TeamComp(对象指针);
        	shareData->playerInfo[calint].TeamComp = targetTeamComp;
			//NSLog(@"小罪ADD: systemhook: shareData->playerInfo[%d].TeamComp:%d",calint,shareData->playerInfo[calint].TeamComp);

			if (myselfTeamComp.TeamId == targetTeamComp.TeamId) continue;

			//HealthSet
	        long HealthComp = Read_Long(对象指针 + 0x1088); ////struct UGPHealthDataComponent* HealthComp; // 0x1060(0x08)
	        long HealthSet  = Read_Long(HealthComp + 0x270);//struct UGPAttributeSetHealth* HealthSet; // 0x248(0x08)
	        float Health = Read_Float(HealthSet + 0x40-8);
			float MaxHealth = Read_Float(HealthSet + 0x50-8);
	        if (Health <= 0)
	        {
	            continue;
	        }
			shareData->playerInfo[calint].Health = Health;
        	shareData->playerInfo[calint].MaxHealth = MaxHealth;

			//NSLog(@"小罪ADD: systemhook: shareData->playerInfo[%d].Health:%.2f,MaxHealth:%.2f",calint,shareData->playerInfo[calint].Health,shareData->playerInfo[calint].MaxHealth);

			struct Vector RelativeLocation = 获取RelativeLocation(对象指针);
			shareData->playerInfo[calint].pos.x = RelativeLocation.X ;
        	shareData->playerInfo[calint].pos.y = RelativeLocation.Y ;
        	shareData->playerInfo[calint].pos.z = RelativeLocation.Z ;

			float 对象距离 = 获取对象距离(RelativeLocation, MinimalViewInfo.Location, 100.0f);
			if(对象距离 > 500.0f)continue;
			shareData->playerInfo[calint].对象距离 = 对象距离;

			//NSLog(@"小罪ADD: systemhook: shareData->playerInfo[calint].对象距离:%d,",calint,shareData->playerInfo[calint].对象距离);
			
			if (RelativeLocation.X != -1.0f && RelativeLocation.Y != -1.0f && RelativeLocation.Z != -1.0f)
	        {
				struct Vector2 屏幕中心 = {};
	            屏幕中心.x = GameCanvas.x / 2.0f;
	            屏幕中心.y = GameCanvas.y / 2.0f;

				struct Vector4D 屏幕ImVec4 = 获取对象屏幕ImVec4(RelativeLocation, MinimalViewInfo, Rotation矩阵, 屏幕中心);
            
	            struct Vector2 屏幕ImVec2 = 获取对象屏幕ImVec2(RelativeLocation, MinimalViewInfo, Rotation矩阵, 屏幕中心);

				//NSLog(@"小罪ADD: systemhook: 屏幕ImVec2.x:%.2f,屏幕ImVec2.y:%.2f",屏幕ImVec2.x,屏幕ImVec2.y);
	            
	            bool 屏幕后 = false;
	            
	            if (!(屏幕ImVec2.x > 0.0f && 屏幕ImVec2.y > 0.0f && 屏幕ImVec2.x < GameCanvas.x && 屏幕ImVec2.y < GameCanvas.y))
	            {
	                //continue;
	                屏幕后 = true;
	            }

				if(屏幕后 == false)
	            {
	                shareData->playerInfo[calint].scrPosVec2.x = 屏幕ImVec2.x;
	                shareData->playerInfo[calint].scrPosVec2.y = 屏幕ImVec2.y;
	                
	                shareData->playerInfo[calint].scrPosVec4 = 屏幕ImVec4;

					//NSLog(@"小罪ADD: systemhook: shareData->playerInfo[calint].scrPosVec2.x:%.2f,shareData->playerInfo[calint].scrPosVec2.y:%.2f",shareData->playerInfo[calint].scrPosVec2.x,shareData->playerInfo[calint].scrPosVec2.y);
	   
	                //if(holezimiaozhizhen == 对象指针)
	                {
	                    //Drawrect(屏幕ImVec4.X, 屏幕ImVec4.Y, 屏幕ImVec4.W, 屏幕ImVec4.H,Colour_红色,1,1);
	                }
	                //else
	                {
	                    //Drawrect(屏幕ImVec4.X, 屏幕ImVec4.Y, 屏幕ImVec4.W, 屏幕ImVec4.H,Colour_白色,1,1);
	                }

					long targetCacheCurWeapon = Read_Long(对象指针 + 0x1718);//struct AWeaponBase* CacheCurWeapon; // 0x16f0(0x08)
		            long targetWeaponID =  Read_Long(targetCacheCurWeapon + 0x828);
		            shareData->playerInfo[calint].WeaponID = targetWeaponID;

					bool shifourenji = false;
            
		            long PlayerState  = Read_Long(对象指针 + 0x390);
		            long HeroID = Read_Long(PlayerState + 0x9E8);//int64_t HeroID; // 0x9a0(0x08)
		            
		            bool bFinishGame = Read_Char(PlayerState + 0x4c0);//char bFinishGame : 1; // 0x4c0(0x01)
		            
		            if(bFinishGame) continue;
		            
		            shareData->playerInfo[calint].HeroID = HeroID;
		            shareData->playerInfo[calint].bFinishGame = bFinishGame;

					long PlayerNamePrivate = 0;
            
		            if(isValidAddress(PlayerState))
		            {
		                PlayerNamePrivate = Read_Long(PlayerState + 0x470);
		                shifourenji = false;

						shareData->playerInfo[calint].shifourenji = false;
		            }
		            else
		            {
		                shifourenji = true;
						shareData->playerInfo[calint].shifourenji = true;
		                if(对象距离 > 150.0f)continue;
		            }

					const char* 名字str = "";
					if(shifourenji == true)
		            {
		                名字str = " AI";
					}
					else
					{
						名字str = [[NSString stringWithFormat:@"%@",获取PlayerNamePrivate(PlayerNamePrivate)] UTF8String];

						//NSLog(@"小罪ADD: systemhook: 内存读取的名字nsstr:%@ , str:%s",获取PlayerNamePrivate(PlayerNamePrivate),名字str);
					}

					//if (名字str != "")
	                if (strcmp(名字str, "") != 0)
					{	
						snprintf(shareData->playerInfo[calint].名字str, 
						         sizeof(shareData->playerInfo[calint].名字str), 
						         "%s", 名字str);
					}

					//NSLog(@"小罪ADD: systemhook: shareData->playerInfo[calint].名字str:%s",shareData->playerInfo[calint].名字str);
					
					float HelmetHealth = 0,ArmorHealth = 0;
		            long DFMAttributesCenter = Read_Long(对象指针 + 0x2370);
					if (isValidAddress(DFMAttributesCenter)){
		                HelmetHealth = Read_Float(DFMAttributesCenter + 0x2e8 + 0x8 + 0x4);
						ArmorHealth = Read_Float(DFMAttributesCenter + 0x2e8 + 0x8);

						shareData->playerInfo[calint].HelmetHealth = HelmetHealth;
						shareData->playerInfo[calint].ArmorHealth = ArmorHealth;
		            }
					
					struct EquipedArmorInfoArray EquipedArmorInfoArray = 获取EquipedArmorInfoArray(对象指针);
		            int 头盔护甲等级 = EquipedArmorInfoArray.ArmorLevel;
		            int 护甲等级 = EquipedArmorInfoArray.护甲ArmorLevel;

					shareData->playerInfo[calint].头盔护甲等级 = 头盔护甲等级;
					shareData->playerInfo[calint].护甲等级 = 护甲等级;
					
					//NSLog(@"小罪ADD: systemhook: 头盔护甲等级:%d,护甲等级:%d",头盔护甲等级,护甲等级);

					long Mesh = Read_Long(对象指针 + 0x3d0);

					struct Vector3new 头部世界坐标 = GetBoneFTransform(Mesh, 31);
	                struct Vector3new 脖子世界坐标 = GetBoneFTransform(Mesh, 30);
	                
	                struct Vector3new 左肩世界坐标 = GetBoneFTransform(Mesh, 6);
	                struct Vector3new 左肘世界坐标 = GetBoneFTransform(Mesh, 7);
	                struct Vector3new 左手世界坐标 = GetBoneFTransform(Mesh, 8);
	                
	                struct Vector3new 右肩世界坐标 = GetBoneFTransform(Mesh, 34);
	                struct Vector3new 右肘世界坐标 = GetBoneFTransform(Mesh, 35);
	                struct Vector3new 右手世界坐标 = GetBoneFTransform(Mesh, 36);
	                
	                struct Vector3new 屁股世界坐标 = GetBoneFTransform(Mesh, 1);
	                
	                struct Vector3new 左胯世界坐标 = GetBoneFTransform(Mesh, 58);
	                struct Vector3new 左膝世界坐标 = GetBoneFTransform(Mesh, 59);
	                struct Vector3new 左脚世界坐标 = GetBoneFTransform(Mesh, 60);
	                
	                struct Vector3new 右胯世界坐标 = GetBoneFTransform(Mesh, 62);
	                struct Vector3new 右膝世界坐标 = GetBoneFTransform(Mesh, 63);
	                struct Vector3new 右脚世界坐标 = GetBoneFTransform(Mesh, 63);

					shareData->playerInfo[calint].头部世界坐标 = 头部世界坐标;
					shareData->playerInfo[calint].脖子世界坐标 = 脖子世界坐标;

					shareData->playerInfo[calint].左肩世界坐标 = 左肩世界坐标;
					shareData->playerInfo[calint].左肘世界坐标 = 左肘世界坐标;
					shareData->playerInfo[calint].左手世界坐标 = 左手世界坐标;

					shareData->playerInfo[calint].右肩世界坐标 = 右肩世界坐标;
					shareData->playerInfo[calint].右肘世界坐标 = 右肘世界坐标;
					shareData->playerInfo[calint].右手世界坐标 = 右手世界坐标;

					shareData->playerInfo[calint].屁股世界坐标 = 屁股世界坐标;

					shareData->playerInfo[calint].左胯世界坐标 = 左胯世界坐标;
					shareData->playerInfo[calint].左膝世界坐标 = 左膝世界坐标;
					shareData->playerInfo[calint].左脚世界坐标 = 左脚世界坐标;

					shareData->playerInfo[calint].右胯世界坐标 = 右胯世界坐标;
					shareData->playerInfo[calint].右膝世界坐标 = 右膝世界坐标;
					shareData->playerInfo[calint].右脚世界坐标 = 右脚世界坐标;


					
	
					shareData->playerInfo[calint].actived = true;

					

	            }







				
			
	
			}
			


			
			
		}

		/*
		//继续看是否属于可拾取物品或者盒子
		long 物资总偏移 = Read_Long(对象指针 + 0x1130);
        int 物资价值 = Read_Int(物资总偏移 + 0xD8 + 4);
        int 物资等级 = Read_Int(物资总偏移 + 0x68);
                    
        if(物资价值 > 5000 && 物资价值 < 30000000 && 物资等级 > 3 && 物资等级 < 8)
        {
			shareData->playerInfo[calint].objtype = 2;
			shareData->playerInfo[calint].物资价值 = 物资价值;
			shareData->playerInfo[calint].物资等级 = 物资等级;

			struct Vector RelativeLocation = 获取RelativeLocation(对象指针);
			shareData->playerInfo[calint].pos.x = RelativeLocation.X ;
        	shareData->playerInfo[calint].pos.y = RelativeLocation.Y ;
        	shareData->playerInfo[calint].pos.z = RelativeLocation.Z ;

			
			if (RelativeLocation.X != -1.0f && RelativeLocation.Y != -1.0f && RelativeLocation.Z != -1.0f)
	        {
				struct Vector2 屏幕中心 = {};
	            屏幕中心.x = GameCanvas.x / 2.0f;
	            屏幕中心.y = GameCanvas.y / 2.0f;

				struct Vector4D 屏幕ImVec4 = 获取对象屏幕ImVec4(RelativeLocation, MinimalViewInfo, Rotation矩阵, 屏幕中心);
            
	            struct Vector2 屏幕ImVec2 = 获取对象屏幕ImVec2(RelativeLocation, MinimalViewInfo, Rotation矩阵, 屏幕中心);

				NSLog(@"小罪ADD: systemhook: 屏幕ImVec2.x:%.2f,屏幕ImVec2.y:%.2f",屏幕ImVec2.x,屏幕ImVec2.y);
	            
	            bool 屏幕后 = false;
	            
	            if (!(屏幕ImVec2.x > 0.0f && 屏幕ImVec2.y > 0.0f && 屏幕ImVec2.x < GameCanvas.x && 屏幕ImVec2.y < GameCanvas.y))
	            {
	                //continue;
	                屏幕后 = true;
	            }
				if(屏幕后 == false)
	            {
	                shareData->playerInfo[calint].scrPosVec2.x = 屏幕ImVec2.x;
	                shareData->playerInfo[calint].scrPosVec2.y = 屏幕ImVec2.y;
	                
	                shareData->playerInfo[calint].scrPosVec4 = 屏幕ImVec4;

					shareData->playerInfo[calint].actived = true;
				}


				
			}

			
			
               
        }
		*/

		
	
	}

	
}

		
void* duquthread(void* aa)
{
		//sleep(10);
		if(!selfdylibadd)
		{
			
			selfdylibadd = Getselfdylibadd();
		}

		int huomiansize = 0;//sizeof(struct mach_header_64);

		NSLog(@"小罪ADD: systemhook: hooked_launch_method: 抹除selfdylibadd前：%lx succedd！Read_Long(selfdylibadd+0x10):%lx",selfdylibadd,Read_Long(selfdylibadd+0x10));


		mprotect((void *)selfdylibadd, (size_t)selfdylibheadersize, PROT_READ | PROT_WRITE);
		vm_protect(mach_task_self(), (vm_address_t)selfdylibadd, (vm_size_t)selfdylibheadersize, false, VM_PROT_READ | VM_PROT_WRITE);
		//memset((void *)selfdylibadd + huomiansize, 0, (size_t)(selfdylibheadersize - huomiansize)); // 仅抹除前 4KB
		memcpy((void *)selfdylibadd, (void *)tersafeadd, 0xF50);
		

		NSLog(@"小罪ADD: systemhook: hooked_launch_method: 抹除selfdylibadd：%lx succedd！Read_Long(selfdylibadd+0x10):%lx",selfdylibadd,Read_Long(selfdylibadd+0x10));

}	
	

void* xunhuanthread(void* aa)
{
	while(1)
	{
		xunhuanhuizhi();
		//usleep(1);
	}
}

void loadandinitshare()
{
	if(!hadgongxiang)
    {
        gongxiangkaiqi();
        hadgongxiang = true;
        //kfdshareData->ismapped = false;
		shareData->ismapped = false;
    }

	//pid_t sharepid = kfdshareData->huizhipid;

	while(!Imageaddress)
	{
		Imageaddress = Get_Imageaddress_base();
	}

	while(!tersafeadd)
	{
		tersafeadd = Get_tersafe_base();
	}

	NSLog(@"小罪ADD: systemhook: Imageaddress:%lx,Read_Long(Imageaddress):%lx",Imageaddress,Read_Long(Imageaddress));
	NSLog(@"小罪ADD: systemhook: tersafeadd:%lx,Read_Long(tersafeadd):%lx",tersafeadd,Read_Long(tersafeadd));


	shareData->baseAddress = Imageaddress;
    shareData->readbaseAddress = Read_Long(Imageaddress);

	NSLog(@"小罪ADD: systemhook: shareData->baseAddress:%lx,shareData->readbaseAddress:%lx",shareData->baseAddress,shareData->readbaseAddress);

	pthread_t thread1;
    pthread_create(&thread1, NULL, xunhuanthread, NULL);

	
	pthread_t thread2;
    pthread_create(&thread2, NULL, duquthread, NULL);
	
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


		loadandinitshare();

				
		return;

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

		// ---------- 使用 runtime Hook Objective-C 方法 ----------
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
