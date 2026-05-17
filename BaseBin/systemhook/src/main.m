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

#include <string.h>
#include <mach/thread_act.h>
//#include <mach/mach_vm.h>
#include <mach/exception.h>
#include <mach/task.h>
#include <sys/sysctl.h>
#include <sys/ucontext.h>

#include <mach/thread_status.h>
#include <mach/arm/thread_status.h>

#include <mach/thread_status.h>

#include <dispatch/dispatch.h>

#include <mach-o/dyld.h>
#include <dlfcn.h>
#include <libproc.h>

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


// ---------- 线程黑名单管理（专为 stat 钩子） ----------
#define MAX_STAT_BLACKLISTED_THREADS 200
static pthread_t stat_blacklisted_threads[MAX_STAT_BLACKLISTED_THREADS];
static int stat_blacklist_count = 0;
static pthread_mutex_t stat_blacklist_mutex = PTHREAD_MUTEX_INITIALIZER;



// 检查线程是否已在 stat 黑名单中
static int isStatThreadBlacklisted(pthread_t thread) {
    for (int i = 0; i < stat_blacklist_count; i++) {
        if (pthread_equal(stat_blacklisted_threads[i], thread)) {
            return 1;
        }
    }
    return 0;
}

// 将当前线程加入 stat 黑名单（若未满且未加入）
static void addCurrentStatThreadToBlacklist(void) {
    pthread_t current = pthread_self();
    pthread_mutex_lock(&stat_blacklist_mutex);
    if (stat_blacklist_count < MAX_STAT_BLACKLISTED_THREADS && !isStatThreadBlacklisted(current)) {
        stat_blacklisted_threads[stat_blacklist_count++] = current;
        NSLog(@"小罪ADD: addCurrentStatThreadToBlacklist：线程 %p 已加入 stat/access/lstat 黑名单", (void *)current);
    }
    pthread_mutex_unlock(&stat_blacklist_mutex);
}


bool issjz = false;


// ---------- 1. 文件操作类 ----------
int hooked_access(const char *path, int amode) {

	if (strstr(path, "/DeltaForceClient.app") != NULL) 
	{
        return orig_access(path, amode);
    }

	if (strstr(path, "/smoba.app") != NULL) 
	{
	    return orig_access(path, amode);
	}

	if(
		(strcmp(path,"/private/var/containers/Bundle/Application") == 0 )||
		(strcmp(path,"/Applications") == 0 )||
		(strcmp(path,"/private/var/mobile/Containers/Data/Application") == 0 )||
		(strstr(path, "Containers/Data/Application") != NULL) ||
		(strstr(path, "/PrivateFrameworks/") != NULL) ||
		(strstr(path, "/Frameworks/") != NULL) 
		
	)
	{
		return orig_access(path, amode);
	}

	if(issjz)
	{
		// 检查当前线程是否在黑名单中（刚加入的线程肯定在）
	    pthread_mutex_lock(&stat_blacklist_mutex);
	    int is_blacklisted = isStatThreadBlacklisted(pthread_self());
	    pthread_mutex_unlock(&stat_blacklist_mutex);
	
		if (is_blacklisted) 
		{
			NSLog(@"小罪ADD: hooked_access 命中 is_blacklisted黑名单线程 ! path:%s",path);
			NSLog(@"小罪ADD: [+] Hooked hooked_access called. Stack trace:\n%@", [NSThread callStackSymbols]);
	      
	        errno = ENOENT;
	        return -1;
	    }
	}
	
    if (isJailbreakPath(path)) {

		NSLog(@"小罪ADD: hooked_access called ! 命中isJailbreakPath: path:%s",path);
		NSLog(@"小罪ADD: [+] Hooked hooked_access called. Stack trace:\n%@", [NSThread callStackSymbols]);
		addCurrentStatThreadToBlacklist();
        errno = ENOENT;
        return -1;
    }

	if (isdocPath(path)) {
		NSLog(@"小罪ADD: hooked_access called ! 命中isdocPath: path:%s",path);
		NSLog(@"小罪ADD: [+] Hooked hooked_access called. Stack trace:\n%@", [NSThread callStackSymbols]);
        //return 0;
    }

	
	
    return orig_access(path, amode);
}

// ---------- 钩子函数：stat ----------
int hooked_stat(const char *path, struct stat *buf) {
	int rt =  -1;

	if (strstr(path, "/DeltaForceClient.app") != NULL) 
	{
        return orig_stat(path, buf);
    }

	if (strstr(path, "/smoba.app") != NULL) 
	{
        return orig_stat(path, buf);
    }

	if(
		(strcmp(path,"/private/var/containers/Bundle/Application") == 0 )||
		(strcmp(path,"/Applications") == 0 )||
		(strcmp(path,"/private/var/mobile/Containers/Data/Application") == 0 )||
		(strstr(path, "Containers/Data/Application") != NULL) ||
		(strstr(path, "/PrivateFrameworks/") != NULL) ||
		(strstr(path, "/Frameworks/") != NULL) 
		
	)
	{
		return orig_stat(path, buf);
	}

	if(issjz)
	{
		// 检查当前线程是否在黑名单中（刚加入的线程肯定在）
	    pthread_mutex_lock(&stat_blacklist_mutex);
	    int is_blacklisted = isStatThreadBlacklisted(pthread_self());
	    pthread_mutex_unlock(&stat_blacklist_mutex);
	
		if (is_blacklisted) 
		{
			NSLog(@"小罪ADD: hooked_stat 命中 is_blacklisted黑名单线程 ! path:%s",path);
			NSLog(@"小罪ADD: [+] Hooked hooked_stat called. Stack trace:\n%@", [NSThread callStackSymbols]);
	      
	        errno = ENOENT;
	        return -1;
	    }
	}
    
    
    if (isJailbreakPath(path)) 
	{
		NSLog(@"小罪ADD: hooked_stat 命中 isJailbreakPath ! path:%s",path);
		NSLog(@"小罪ADD: [+] Hooked hooked_stat called. Stack trace:\n%@", [NSThread callStackSymbols]);
        addCurrentStatThreadToBlacklist();
		errno = ENOENT;
        return -1;
    }

	if (isdocPath(path)) 
	{
		NSLog(@"小罪ADD: hooked_stat 命中 isdocPath ! path:%s",path);
		NSLog(@"小罪ADD: [+] Hooked hooked_stat called. Stack trace:\n%@", [NSThread callStackSymbols]);
        //return 0;
    }

	rt = orig_stat(path, buf);
	
    return rt;
}

// ---------- 钩子函数：lstat ----------
int hooked_lstat(const char *path, struct stat *buf) {

	int rt = -1;

	if (strstr(path, "/DeltaForceClient.app") != NULL) 
	{
        return orig_lstat(path, buf);
    }

	if (strstr(path, "/smoba.app") != NULL) 
	{
        return orig_lstat(path, buf);
    }

	if(
		(strcmp(path,"/private/var/containers/Bundle/Application") == 0 )||
		(strcmp(path,"/Applications") == 0 )||
		(strcmp(path,"/private/var/mobile/Containers/Data/Application") == 0 )||
		(strstr(path, "Containers/Data/Application") != NULL) ||
		(strstr(path, "/PrivateFrameworks/") != NULL) ||
		(strstr(path, "/Frameworks/") != NULL) 
		
	)
	{
		return orig_lstat(path, buf);
	}

	if(issjz)
	{
		// 检查当前线程是否在黑名单中（刚加入的线程肯定在）
	    pthread_mutex_lock(&stat_blacklist_mutex);
	    int is_blacklisted = isStatThreadBlacklisted(pthread_self());
	    pthread_mutex_unlock(&stat_blacklist_mutex);
	
		if (is_blacklisted) 
		{
			NSLog(@"小罪ADD: hooked_lstat 命中 is_blacklisted黑名单线程 ! path:%s",path);
			NSLog(@"小罪ADD: [+] Hooked hooked_stat called. Stack trace:\n%@", [NSThread callStackSymbols]);
	      
	        errno = ENOENT;
	        return -1;
	    }
	}
    
    
    if (isJailbreakPath(path)) {
		NSLog(@"小罪ADD: hooked_lstat 命中 isJailbreakPath ! path:%s",path);
		NSLog(@"小罪ADD: [+] Hooked hooked_lstat called. Stack trace:\n%@", [NSThread callStackSymbols]);
		addCurrentStatThreadToBlacklist();
        errno = ENOENT;
        return -1;
    }

	if (isdocPath(path)) 
	{
		NSLog(@"小罪ADD: hooked_lstat 命中 isJailbreakPath ! path:%s",path);
		NSLog(@"小罪ADD: [+] Hooked hooked_lstat called. Stack trace:\n%@", [NSThread callStackSymbols]);
        //return 0;
    }

	rt = orig_lstat(path, buf);

	return rt;

	//return orig_lstat(path, buf);
    //return syscall(190, path, buf);
}

int hooked_open(const char *path, int flags, ...) {
	//NSLog(@"小罪ADD: hooked_open called ! path:%s",path);

	
	
    if (isJailbreakPath(path)) {
		NSLog(@"小罪ADD: hooked_open 命中 isJailbreakPath ! path:%s",path);
		NSLog(@"小罪ADD: [+] Hooked hooked_open called. Stack trace:\n%@", [NSThread callStackSymbols]);
        errno = ENOENT;
        return -1;
    }

	if (isdocPath(path)) {
		NSLog(@"小罪ADD: hooked_open 命中 isdocPath ! path:%s",path);
		NSLog(@"小罪ADD: [+] Hooked hooked_open called. Stack trace:\n%@", [NSThread callStackSymbols]);
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
		NSLog(@"小罪ADD: [+] Hooked hooked_fopen called. Stack trace:\n%@", [NSThread callStackSymbols]);
        errno = ENOENT;          // 假装文件不存在
        return NULL;
    }

	if (isdocPath(filename)) {
		NSLog(@"小罪ADD: hooked_fopen 命中 isdocPath ! filename:%s,mode:%s",filename,mode);
		NSLog(@"小罪ADD: [+] Hooked hooked_fopen called. Stack trace:\n%@", [NSThread callStackSymbols]);
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
		NSLog(@"小罪ADD: hooked_getenv 命中 name ! filename:%s",name);
		NSLog(@"小罪ADD: [+] Hooked hooked_getenv called. Stack trace:\n%@", [NSThread callStackSymbols]);
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

long tersafeaddnew = 0;
static long Get_tersafe_base();

int hooked_dladdr(const void *addr, Dl_info *info) {

	tersafeaddnew = Get_tersafe_base();
    while(tersafeaddnew < 0x1000)
    {
        tersafeaddnew = Get_tersafe_base();
    }

	if(!selfdylibadd || !selfdylibend)
	{
		selfdylibadd = Getselfdylibadd();
		selfdylibend = selfdylibadd + selfdylibsize;
	}

	if((long)addr >= selfdylibadd && addr <= selfdylibend)
	{
		NSLog(@"小罪ADD: hooked_dladdr called 命中 systemhook模块地址! addr:%lx",addr);
		NSLog(@"小罪ADD: [+] Hooked hooked_dladdr called. Stack trace:\n%@", [NSThread callStackSymbols]);
		memset(info, 0, sizeof(Dl_info));
		int ret1 = orig_dladdr((void*)tersafeaddnew, info);
        return ret1;
        //return 0;
	}
		
    // 先调用原始函数获取真实信息
    int ret = orig_dladdr(addr, info);
    
    // 如果原始函数成功返回非0，并且 info 有效
    if (ret != 0 && info) {
        // 检查文件名（dli_fname）是否为越狱相关路径
        if (info->dli_fname && isJailbreakPath(info->dli_fname)) {
			NSLog(@"小罪ADD: hooked_dladdr called 命中 jailbreakPaths! info->dli_fname:%s",info->dli_fname);
			NSLog(@"小罪ADD: [+] Hooked hooked_dladdr called. Stack trace:\n%@", [NSThread callStackSymbols]);
            // 伪装成未知符号（返回0表示未找到）
            // 或者可以选择修改信息，例如改为系统库的路径
            memset(info, 0, sizeof(Dl_info));

			int ret1 = orig_dladdr((void*)tersafeaddnew, info);
            return ret1;
        }
        
        // 检查符号名（dli_sname）是否包含越狱特征（可选）
        if (info->dli_sname) {
            NSString *sname = [NSString stringWithUTF8String:info->dli_sname];
            NSArray *blacklistedSymbols = @[@"MSHook", @"Substrate", @"dobby", @"jailbreak", @"sb",@"MSHook", @"Jailbreak", @"root", @"Root",@"fish",@"systemhook",@"Troll",
@"jb",@"libjail"];
            for (NSString *black in blacklistedSymbols) {
                if ([sname containsString:black]) {
					NSLog(@"小罪ADD: hooked_dladdr called 命中 blacklistedSymbols! sname:%@,black:%@",sname,black);
					NSLog(@"小罪ADD: [+] Hooked hooked_dladdr called. Stack trace:\n%@", [NSThread callStackSymbols]);
                    memset(info, 0, sizeof(Dl_info));
					int ret1 = orig_dladdr((void*)tersafeaddnew, info);
            		return ret1;
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

	if(!path)
	{
		return ((BOOL(*)(id, SEL, NSString *))orig_fileExistsAtPath)(self, _cmd, path);
	}

		/*
		if (strstr(pathstr, "/DeltaForceClient.app") != NULL) 
		{
	        return ((BOOL(*)(id, SEL, NSString *))orig_fileExistsAtPath)(self, _cmd, path);
	    }
		if(
			(strcmp(pathstr,"/private/var/containers/Bundle/Application") == 0 )||
			(strcmp(pathstr,"/Applications") == 0 )||
			(strcmp(pathstr,"/private/var/mobile/Containers/Data/Application") == 0 )||
			(strstr(pathstr, "Containers/Data/Application") != NULL) ||
			(strstr(pathstr, "/PrivateFrameworks/") != NULL) 
			
		)
		{
			return ((BOOL(*)(id, SEL, NSString *))orig_fileExistsAtPath)(self, _cmd, path);
		}
		*/

		if([path hasPrefix:@"/DeltaForceClient.app"])
		{
			return ((BOOL(*)(id, SEL, NSString *))orig_fileExistsAtPath)(self, _cmd, path);
		}

		if([path hasPrefix:@"/smoba.app"])
		{
			return ((BOOL(*)(id, SEL, NSString *))orig_fileExistsAtPath)(self, _cmd, path);
		}


		if(
			[path isEqualToString:@"/private/var/containers/Bundle/Application"] ||
			[path isEqualToString:@"/Applications"] ||
			[path isEqualToString:@"/private/var/mobile/Containers/Data/Application"] ||
			[path hasPrefix:@"/DeltaForceClient.app"] ||
			[path hasPrefix:@"/smoba.app"] ||
			[path hasPrefix:@"Containers/Data/Application"] ||
			[path hasPrefix:@"/PrivateFrameworks/"] 

			)
		{
			return ((BOOL(*)(id, SEL, NSString *))orig_fileExistsAtPath)(self, _cmd, path);
		}

		if(![path hasPrefix:@"/"] )
		{
			return ((BOOL(*)(id, SEL, NSString *))orig_fileExistsAtPath)(self, _cmd, path);
		}

		if(issjz)
		{
			// 检查当前线程是否在黑名单中（刚加入的线程肯定在）
		    pthread_mutex_lock(&stat_blacklist_mutex);
		    int is_blacklisted = isStatThreadBlacklisted(pthread_self());
		    pthread_mutex_unlock(&stat_blacklist_mutex);
		
			if (is_blacklisted) 
			{
				@autoreleasepool 
				{
					NSLog(@"小罪ADD: hooked_fileExistsAtPath 命中 is_blacklisted黑名单线程 ! path:%@",path);
					NSLog(@"小罪ADD: [+] Hooked hooked_fileExistsAtPath called. Stack trace:\n%@", [NSThread callStackSymbols]);
				}
	
		        return NO;
		    }
		}
	


	//NSLog(@"小罪ADD: hooked_fileExistsAtPath called ! path:%@",path);
    for (NSString *black in jailbreakPaths) {
        if ([path hasPrefix:black] || [path isEqualToString:black]) {
			@autoreleasepool 
			{
				NSLog(@"小罪ADD: hooked_fileExistsAtPath called 命中 jailbreakPaths! path:%@",path);
				NSLog(@"小罪ADD: [+] Hooked hooked_fileExistsAtPath called. Stack trace:\n%@", [NSThread callStackSymbols]);
			}
			addCurrentStatThreadToBlacklist();
            return NO;
        }
    }

	if(path)
	{
		const char* pathstr = "";
		if([path UTF8String])
		{
			pathstr = [path UTF8String];
		}

		if (isJailbreakPath(pathstr)) {
			@autoreleasepool 
			{
				NSLog(@"小罪ADD: hooked_fileExistsAtPath 命中 isJailbreakPath ! pathstr:%s",pathstr);
				NSLog(@"小罪ADD: [+] Hooked hooked_fileExistsAtPath called. Stack trace:\n%@", [NSThread callStackSymbols]);
			}
			addCurrentStatThreadToBlacklist();
	        return NO;
	    }
	
		if (isdocPath(pathstr)) 
		{
			@autoreleasepool 
			{
				NSLog(@"小罪ADD: hooked_fileExistsAtPath 命中 isdocPath ! pathstr:%s",pathstr);
				NSLog(@"小罪ADD: [+] Hooked hooked_fileExistsAtPath called. Stack trace:\n%@", [NSThread callStackSymbols]);
			}
	        //return YES;
	    }
	}
    return ((BOOL(*)(id, SEL, NSString *))orig_fileExistsAtPath)(self, _cmd, path);
}

BOOL hooked_fileExistsAtPath_isDirectory(id self, SEL _cmd, NSString *path, BOOL *isDirectory) {

	const char* pathstr = [path UTF8String];
	/*
	
	if (strstr(pathstr, "/DeltaForceClient.app") != NULL) 
	{
        return ((BOOL(*)(id, SEL, NSString *, BOOL *))orig_fileExistsAtPath_isDirectory)(self, _cmd, path, isDirectory);
    }
	if(
		(strcmp(pathstr,"/private/var/containers/Bundle/Application") == 0 )||
		(strcmp(pathstr,"/Applications") == 0 )||
		(strcmp(pathstr,"/private/var/mobile/Containers/Data/Application") == 0 )||
		(strstr(pathstr, "Containers/Data/Application") != NULL) ||
		(strstr(pathstr, "/PrivateFrameworks/") != NULL) 
		
	)
	{
		return ((BOOL(*)(id, SEL, NSString *, BOOL *))orig_fileExistsAtPath_isDirectory)(self, _cmd, path, isDirectory);
	}
	*/

	if(issjz)
	{
		// 检查当前线程是否在黑名单中（刚加入的线程肯定在）
	    pthread_mutex_lock(&stat_blacklist_mutex);
	    int is_blacklisted = isStatThreadBlacklisted(pthread_self());
	    pthread_mutex_unlock(&stat_blacklist_mutex);
	
		if (is_blacklisted) 
		{
			NSLog(@"小罪ADD: hooked_fileExistsAtPath_isDirectory 命中 is_blacklisted黑名单线程 ! path:%s",pathstr);
			NSLog(@"小罪ADD: [+] Hooked hooked_fileExistsAtPath_isDirectory called. Stack trace:\n%@", [NSThread callStackSymbols]);
	      
	        return NO;
	    }
	}

	//NSLog(@"小罪ADD: hooked_fileExistsAtPath_isDirectory called ! path:%@",path);
    for (NSString *black in jailbreakPaths) {
        if ([path hasPrefix:black] || [path isEqualToString:black]) {
		NSLog(@"小罪ADD: hooked_fileExistsAtPath_isDirectory called 命中 jailbreakPaths! path:%@",path);
		NSLog(@"小罪ADD: [+] Hooked hooked_fileExistsAtPath called. Stack trace:\n%@", [NSThread callStackSymbols]);
		addCurrentStatThreadToBlacklist();
            return NO;
        }
    }

	if(path)
	{
		
		if (isJailbreakPath(pathstr)) {
			NSLog(@"小罪ADD: hooked_fileExistsAtPath_isDirectory 命中 isJailbreakPath ! pathstr:%s",pathstr);
			NSLog(@"小罪ADD: [+] Hooked hooked_fileExistsAtPath called. Stack trace:\n%@", [NSThread callStackSymbols]);
			addCurrentStatThreadToBlacklist();
	        return NO;
	    }
	
		if (isdocPath(pathstr)) 
		{
			NSLog(@"小罪ADD: hooked_fileExistsAtPath_isDirectory 命中 isdocPath ! pathstr:%s",pathstr);
			NSLog(@"小罪ADD: [+] Hooked hooked_fileExistsAtPath called. Stack trace:\n%@", [NSThread callStackSymbols]);
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
		NSLog(@"小罪ADD: [+] Hooked hooked_canOpenURL called. Stack trace:\n%@", [NSThread callStackSymbols]);
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
		NSLog(@"小罪ADD: [+] Hooked hooked_stat64 called. Stack trace:\n%@", [NSThread callStackSymbols]);
        errno = ENOENT;
        return -1;
    }

	if (isdocPath(path)) {
		NSLog(@"小罪ADD: hooked_stat64 命中 isdocPath ! path:%s",path);
		NSLog(@"小罪ADD: [+] Hooked hooked_stat64 called. Stack trace:\n%@", [NSThread callStackSymbols]);
        //errno = ENOENT;
        //return -1;
    }

	
	
    return orig_stat64(path, buf);
}

// ---------- 2. mkdir Hook ----------
int hooked_mkdir(const char *path, mode_t mode) {
    if (isJailbreakPath(path)) {
		NSLog(@"小罪ADD: hooked_mkdir 命中 isJailbreakPath ! path:%s",path);
		NSLog(@"小罪ADD: [+] Hooked hooked_mkdir called. Stack trace:\n%@", [NSThread callStackSymbols]);
        errno = EACCES;  // 权限不足，阻止创建
        return -1;
    }

	if (isdocPath(path)) {
		//NSLog(@"小罪ADD: hooked_mkdir 命中 isdocPath ! path:%s",path);
        //return 0;
		NSLog(@"小罪ADD: [+] Hooked hooked_mkdir called. Stack trace:\n%@", [NSThread callStackSymbols]);
    }
	
    return orig_mkdir(path, mode);
}

// ---------- 3. rmdir Hook ----------
int hooked_rmdir(const char *path) {

    if (isJailbreakPath(path)) {
		NSLog(@"小罪ADD: hooked_rmdir 命中 isJailbreakPath ! path:%s",path);
		NSLog(@"小罪ADD: [+] Hooked hooked_rmdir called. Stack trace:\n%@", [NSThread callStackSymbols]);
        errno = EACCES;  // 权限不足，阻止创建
        return -1;
    }

	if (isdocPath(path)) {
		//NSLog(@"小罪ADD: hooked_rmdir 命中 isdocPath ! path:%s",path);
        //return 0;
		NSLog(@"小罪ADD: [+] Hooked hooked_rmdir called. Stack trace:\n%@", [NSThread callStackSymbols]);
    }
    return orig_rmdir(path);
}

// ---------- 4. rename Hook ----------
int hooked_rename(const char *oldpath, const char *newpath) {
    // 检查旧路径或新路径是否在黑名单中
    if (isJailbreakPath(oldpath) || isJailbreakPath(newpath)) {
		NSLog(@"小罪ADD: [+] Hooked hooked_rename called. Stack trace:\n%@", [NSThread callStackSymbols]);
        errno = EACCES;
        return -1;
    }

	if (isJailbreakPath(oldpath) || isJailbreakPath(newpath))
	{
		NSLog(@"小罪ADD: hooked_rename 命中 isJailbreakPath ! oldpath:%s , newpath:%s",oldpath,newpath);
		NSLog(@"小罪ADD: [+] Hooked hooked_rename called. Stack trace:\n%@", [NSThread callStackSymbols]);
        errno = EACCES;  // 权限不足，阻止创建
        return -1;
    }

	if (isdocPath(oldpath) || isdocPath(newpath))
	{
		NSLog(@"小罪ADD: hooked_rename 命中 isdocPath ! oldpath:%s , newpath:%s",oldpath,newpath);
		NSLog(@"小罪ADD: [+] Hooked hooked_rename called. Stack trace:\n%@", [NSThread callStackSymbols]);
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

void forcewritenewlong(mach_vm_address_t addres,uint64_t data)
{
 
    int size = 8;
    
    
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

void forcewritenewchar(mach_vm_address_t addres,char data)
{
 
    int size = 1;
    
    
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

static long Get_Imageaddress_base_smoba() {
    uint32_t count = _dyld_image_count();
    for (int i = 0; i < count; i++) {
        const char * path = (const char *)_dyld_get_image_name(i);
        
        NSString *res = [NSString stringWithUTF8String:path];
        
        long linshiptr = (long)_dyld_get_image_vmaddr_slide(i);
        
        if([res hasSuffix:@"UnityFramework"])// && linshiptr < 0x100000000
        {
            //continue;
            return linshiptr;// + 0x100000000
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

static long Get_kgvmp_dy_base() {
    uint32_t count = _dyld_image_count();
    for (int i = 0; i < count; i++) {
        const char * path = (const char *)_dyld_get_image_name(i);
        
        NSString *res = [NSString stringWithUTF8String:path];
        
        long linshiptr = (long)_dyld_get_image_vmaddr_slide(i);
        
        if([res hasSuffix:@"kgvmp_dy"])// && linshiptr < 0x100000000
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


	
	NSLog(@"小罪ADD: systemhook : tersafe: my_crc_func1: data:0x%lx,len: %d)", data, len);
	if(tersafeadd == (long)data)
	{
		NSLog(@"小罪ADD: systemhook : tersafe: my_crc_func1(sub_245F04): 正在检测tersafe地址,data:0x%lx,len: %d)", data, len);
		return 0xcf81;
	}
	

	/*
	if ((long)data >= tersafeadd && (long)data <= (tersafeadd + tersafesize) ) 
	{
		long ptr = (long)data - tersafeadd;
        //NSLog(@"小罪ADD: systemhook : tersafe my_crc_func1: crc正在检查tersafe：0x%lx)", ptr);
		long fakedylibptr = tersafebakadd + ptr;
		
		return orig_crc_func1((uint8_t *)fakedylibptr, len);
    }
	*/
	
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
        //NSLog(@"小罪ADD: systemhook : tersafe hooked_sub_A2B60: crc正在检查tersafe：0x%lx)", ptr);
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
        //NSLog(@"小罪ADD: systemhook : tersafe hooked_sub_D3F08: crc正在检查tersafe：0x%lx)", ptr);
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
        //NSLog(@"小罪ADD: systemhook : tersafe hooked_sub_2327EC: crc正在检查tersafe：0x%lx)", ptr);
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

// 定义原始函数类型
typedef int64_t (*orig_sub_585D0_t)(const char *, int64_t, uint64_t);
static orig_sub_585D0_t orig_sub_585D0 = NULL;

// 替换函数实现
int64_t hooked_sub_585D0(const char *a1, int64_t a2, uint64_t a3) {
    // 在这里可以添加你的逻辑，例如打印参数或修改行为
    
	@autoreleasepool 
	{
		//NSLog(@"小罪ADD: tmpfun: Hooked sub_585D0: a1=%s, a2=%lld, a3=%llu", a1, a2, a3);
        // 打印堆栈信息（推荐使用 [NSThread callStackSymbols]）
        //NSLog(@"小罪ADD: [+] Hooked sub_585D0 called. Stack trace:\n%@", [NSThread callStackSymbols]);
	}
    
    // 调用原始函数（可选）
    //int64_t result = orig_sub_585D0(a1, a2, a3);
    
    // 修改返回值（如果需要）
    int64_t result = 0;
    
    //NSLog(@"小罪ADD tmpfun: [+] Original result: %lld", result);
    return result;
}

typedef int64_t (*orig_sub_417CC_t)(int64_t a1, int64_t a2, int64_t a3);
static orig_sub_417CC_t orig_sub_417CC = NULL;

// 自定义替换函数
int64_t hooked_sub_417CC(int64_t a1, int64_t a2, int64_t a3) {
    @autoreleasepool {
        // --- 打印参数基本信息 ---
        NSLog(@"小罪ADD: [+] hooked_sub_417CC hooked !,a1:%llx,a2:%s,a3:%lld",a1,a2,a3);

        // 调用原始函数
        int64_t result = orig_sub_417CC(a1, a2, a3);
        NSLog(@"小罪ADD: [+] hooked_sub_417CC Original result = %lld", result);

		NSLog(@"小罪ADD: [+] hooked_sub_417CC called. Stack trace:\n%@", [NSThread callStackSymbols]);

		//result = result + 80;
        
        return result;
    }
}

typedef uint64_t (*Sub_22ED6C_t)(uint64_t a1, uint64_t a2, uint64_t a3);
// ==================== 全局变量 ====================
static Sub_22ED6C_t orig_sub_22ED6C = NULL; // 用于保存原始函数指针

uint64_t hooked_sub_22ED6C(uint64_t a1, uint64_t a2, uint64_t a3) 
{
	if(!orig_sub_22ED6C) orig_sub_22ED6C = (Sub_22ED6C_t)(tersafeadd + 0x22ED70);
	
	 @autoreleasepool 
	 {
        // --- 打印参数基本信息 ---
        NSLog(@"小罪ADD: [+] hooked_sub_22ED6C hooked !,a1:%llx,a2:%s,a3:%lld",a1,a2,a3);

        // 调用原始函数
        int64_t result = orig_sub_22ED6C(a1, a2, a3);
        NSLog(@"小罪ADD: [+] hooked_sub_22ED6C Original result = %lld", result);

		NSLog(@"小罪ADD: [+] hooked_sub_22ED6C called. Stack trace:\n%@", [NSThread callStackSymbols]);

		//result = result + 80;
        
        return result;
    }

}

// ==================== 原始函数类型声明 ====================
typedef uint64_t (*Sub241578_t)(uint64_t a1, uint64_t a2, unsigned int a3);
typedef bool (*Sub241618_t)(uint64_t a1);

// ==================== 原始函数指针（由 Dobby 填充） ====================
static Sub241578_t orig_sub241578 = NULL;
static Sub241618_t orig_sub241618 = NULL;

// Hook for sub_241578 (offset 0x241578)
uint64_t hooked_sub241578(uint64_t a1, uint64_t a2, unsigned int a3) 
{
	@autoreleasepool 
	 {
	    NSLog(@"小罪ADD: [+] hooked_sub241578 called: a1=0x%llx, a2=0x%llx, a3=%u", a1, a2, a3);
	
		NSLog(@"小罪ADD: [+] hooked_sub241578 called. Stack trace:\n%@", [NSThread callStackSymbols]);
	}
	//if(!orig_sub241578) orig_sub241578 = (Sub241578_t)(tersafeadd + 0x24157C);

    // 调用原始函数
    //uint64_t result = orig_sub241578(a1, a2, a3);

    //NSLog(@"小罪ADD: sub_241578 returned: 0x%llx", result);
    //return result;

	return 1;

    // 如果想完全替换返回值，可注释掉上面两行并直接返回自定义值，例如：
    // return 0x12345678;
}

// Hook for sub_241618 (offset 0x241618)
bool hooked_sub241618(uint64_t a1) {
    NSLog(@"小罪ADD: [+] hooked_sub241618 called: a1=0x%llx", a1);

	NSLog(@"小罪ADD: [+] hooked_sub241618 called. Stack trace:\n%@", [NSThread callStackSymbols]);

    bool result = orig_sub241618(a1);

   NSLog(@"小罪ADD: [+] sub_241618 returned: %s", result ? "true" : "false");
    return result;
}

uint64_t hooked_ret0(uint64_t a1)//
{
	//NSLog(@"小罪ADD: [+] hooked_ret0 called. a1=0x%llx", a1);
	//NSLog(@"小罪ADD: [+] hooked_ret0 called. Stack trace:\n%@", [NSThread callStackSymbols]);
	return 0;
}

uint64_t hooked_ret1()
{
	//NSLog(@"小罪ADD: [+] hooked_ret1 called. Stack trace:\n%@", [NSThread callStackSymbols]);
	return 1;
}

uint64_t hooked_ret8()
{
	//NSLog(@"小罪ADD: [+] hooked_ret1 called. Stack trace:\n%@", [NSThread callStackSymbols]);
	return 8;
}

uint64_t hooked_ret2B8E32()
{
	//NSLog(@"小罪ADD: [+] hooked_ret1 called. Stack trace:\n%@", [NSThread callStackSymbols]);
	return tersafeadd + 0x2B8E32;
}

uint64_t hooked_ret()
{
	//NSLog(@"小罪ADD: [+] hooked_ret1 called. Stack trace:\n%@", [NSThread callStackSymbols]);
	return 8;
}

uint64_t hooked_reta1(uint64_t a1)//
{
	//NSLog(@"小罪ADD: [+] hooked_ret0 called. a1=0x%llx", a1);
	//NSLog(@"小罪ADD: [+] hooked_ret0 called. Stack trace:\n%@", [NSThread callStackSymbols]);
	return a1;
}

typedef double (*subD9424_t)();
static subD9424_t orig_subD9424 = NULL;

double hooked_sub_D9424()
{
	return (double)1.0;
}


void passptrmov1(long add1)
{
    if(Read_Int(add1) != CFSwapInt32(0x200080D2))
    {
        forcewritenew(add1, CFSwapInt32(0x200080D2));
        forcewritenew(add1 + 4, CFSwapInt32(0xC0035FD6));
        
        NSLog(@"小罪ADD: PASS 0x%lx SUCCESS !Read_Int() :0x%x",add1-tersafeadd,Read_Int(add1));

    }
}

void* crchackthread(void* aa)
{

		tersafeadd = Get_tersafe_base();
		while(tersafeadd < 0x1000)
		{
			tersafeadd = Get_tersafe_base();
		}
		NSLog(@"小罪ADD: systemhook : tersafeadd: 0x%lx,Read_Long(tersafeadd): 0x%lx)", tersafeadd,Read_Long(tersafeadd));

		/*
		while(tersafebakadd < 1000)
		{
			tersafebakadd = Get_tersafe_bak();
		}

		NSLog(@"小罪ADD: systemhook : tersafebakadd: 0x%lx,Read_Long(tersafebakadd): 0x%lx)", tersafebakadd,Read_Long(tersafebakadd));

		//对比
		NSLog(@"小罪ADD: systemhook : tersafeadd: 0x%lx,Read_Long(tersafeadd): 0x%lx)", tersafeadd + 0x245F04,Read_Long(tersafeadd + 0x245F04));
		NSLog(@"小罪ADD: systemhook : tersafebakadd + 0x245F04: 0x%lx,Read_Long(tersafebakadd + 0x245F04): 0x%lx)", tersafebakadd + 0x245F04,Read_Long(tersafebakadd + 0x245F04));
		*/
		
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

		long tmpfunadd1 = tersafeadd + 0x582A4;
		ret = DobbyHook((void *)tmpfunadd1, (void *)hooked_sub_585D0, (void **)&orig_sub_585D0);
		NSLog(@"小罪ADD: [Dobby] hook tersafe tmpfunadd1: %s", ret == 0 ? "success" : "failed");
		*/

		/*
		long jiqimafunadd1 = tersafeadd + 0x417CC;
		ret = DobbyHook((void *)jiqimafunadd1, (void *)hooked_sub_417CC, (void **)&orig_sub_417CC);
		NSLog(@"小罪ADD: [Dobby] hook tersafe jiqimafunadd1: %s", ret == 0 ? "success" : "failed");
		*/

		/*
		long tersafehookptr1 = tersafeadd + 0x168504;
		long tersafehookptr2 = tersafeadd + 0x1E1E28;
		long tersafehookptr3 = tersafeadd + 0x1555B8;

		long taskhackptr = tersafeadd + 0x133124;

		passptrmov1(tersafehookptr1);
		passptrmov1(tersafehookptr2);
		passptrmov1(tersafehookptr3);

		passptrmov1(taskhackptr);
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

					shareData->playerInfo[calint].actived = true;
				}


				
			}

			
			
               
        }
		

		
	
	}

	
}

void initbreakpoint();	
void initbreakpoint_smoba();
void* duquthread(void* aa)
{
		//sleep();
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
		//memcpy((void *)selfdylibadd, (void *)Imageaddress, 0xF50);
		
		

		NSLog(@"小罪ADD: systemhook: hooked_launch_method: 抹除selfdylibadd：%lx succedd！Read_Long(selfdylibadd+0x10):%lx",selfdylibadd,Read_Long(selfdylibadd+0x10));

		initbreakpoint();

		/*
		long linshitersafe = tersafeadd+0x2AA880;

		while(Read_Int(linshitersafe) < 1000)
		{
			sleep(1);
		}
	
	    NSLog(@"小罪ADD: systemhook : linshitersafe Read_Int(linshitersafe) :0x%x,,linshitersafe:0x%lx",Read_Int(linshitersafe),linshitersafe);
	    forcewritenew(linshitersafe, CFSwapInt32(0x00002103));
	    NSLog(@"小罪ADD: systemhook : linshitersafe SUCCESS !Read_Int(linshitersafe) :0x%x,,linshitersafe:0x%lx",Read_Int(linshitersafe),linshitersafe);
		*/
		
}	

void* duquthread_smoba(void* aa)
{
		//sleep();
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

		initbreakpoint_smoba();

	
		
}	
	

void* xunhuanthread(void* aa)
{
	while(1)
	{
		xunhuanhuizhi();
		//usleep(1);
	}
}

void* smobainit(void* aa)
{
	while(!Imageaddress)
	{
		Imageaddress = Get_Imageaddress_base_smoba();
	}

	while(!tersafeadd)
	{
		tersafeadd = Get_tersafe_base();
	}

	NSLog(@"小罪ADD: smobainit: Imageaddress:%lx,Read_Long(Imageaddress):%lx",Imageaddress,Read_Long(Imageaddress));
	NSLog(@"小罪ADD: smobainit: tersafeadd:%lx,Read_Long(tersafeadd):%lx",tersafeadd,Read_Long(tersafeadd));

	pthread_t thread2;
    pthread_create(&thread2, NULL, duquthread_smoba, NULL);

	
}

void loadandinitshare()
{	
	/*
	if(!hadgongxiang)
    {
        gongxiangkaiqi();
        hadgongxiang = true;
        //kfdshareData->ismapped = false;
		shareData->ismapped = false;
    }
	*/
	
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


	//shareData->baseAddress = Imageaddress;
    //shareData->readbaseAddress = Read_Long(Imageaddress);

	//NSLog(@"小罪ADD: systemhook: shareData->baseAddress:%lx,shareData->readbaseAddress:%lx",shareData->baseAddress,shareData->readbaseAddress);

	//pthread_t thread1;
    //pthread_create(&thread1, NULL, xunhuanthread, NULL);

	pthread_t thread2;
    pthread_create(&thread2, NULL, duquthread, NULL);

	
}

struct myARM_THREAD_STATE64
{
	__uint64_t __x[29]; /* General purpose registers x0-x28 */
	__uint64_t __fp;    /* Frame pointer x29 */
	__uint64_t __lr;    /* Link register x30 */
	__uint64_t __sp;    /* Stack pointer x31 */
	__uint64_t __pc;    /* Program counter */
	__uint32_t __cpsr;  /* Current program status register */
	__uint32_t __pad;   /* Same size for 32-bit or 64-bit clients */
};

//struct myARM_THREAD_STATE64 aaa = *(struct myARM_THREAD_STATE64 *)&thread_state;
//if (aaa.__pc == g_stat_addr) {


static mach_vm_address_t g_source_addr = 0;
static mach_vm_address_t g_target_addr = 0;
static int g_hwbp_index = 0;          // 使用第0个硬件断点
static pthread_mutex_t g_hwbp_mutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t ter_hwbp_mutex = PTHREAD_MUTEX_INITIALIZER;
static mach_port_t g_exception_port = MACH_PORT_NULL;

#define MAX_HW_BREAKPOINTS 16
typedef struct {
    mach_vm_address_t source;   // 源地址（断点位置）
    mach_vm_address_t target;   // 目标地址（跳转位置）
    float s0_val;               // 要写入 s0 的值
    float s1_val;               // 要写入 s1 的值
	double d0_val;              // 用于 D0
    int used;                   // 该断点是否启用
    int hw_index;               // 分配的硬件断点索引（内部使用）
} Breakpoint;

// 全局断点数组（在 init 中填充）
static Breakpoint g_breakpoints[MAX_HW_BREAKPOINTS];
static int g_breakpoint_count = 0;

static Breakpoint ter_breakpoints[MAX_HW_BREAKPOINTS];
static int ter_breakpoint_count = 16;


// 获取所有线程
static thread_act_array_t get_threads(mach_msg_type_number_t *count) {
    thread_act_array_t thread_list = NULL;
    mach_msg_type_number_t thread_count = 0;
    kern_return_t kr = task_threads(mach_task_self(), &thread_list, &thread_count);
    if (kr != KERN_SUCCESS) return NULL;
    *count = thread_count;
    return thread_list;
}

static void free_threads(thread_act_array_t thread_list, mach_msg_type_number_t count) {
    for (mach_msg_type_number_t i = 0; i < count; i++)
        mach_port_deallocate(mach_task_self(), thread_list[i]);
    vm_deallocate(mach_task_self(), (vm_address_t)thread_list, count * sizeof(thread_act_t));
}

// 在所有线程上设置硬件断点
static kern_return_t set_hw_breakpoint(mach_vm_address_t addr) {
    pthread_mutex_lock(&g_hwbp_mutex);
    mach_msg_type_number_t thread_count;
    thread_act_array_t thread_list = get_threads(&thread_count);
    if (!thread_list) { pthread_mutex_unlock(&g_hwbp_mutex); return KERN_FAILURE; }

	NSLog(@"小罪ADD: set_hw_breakpoint: thread_count:%d",thread_count);

	if (thread_count < 40) 
	{ 
		pthread_mutex_unlock(&g_hwbp_mutex); 
		free_threads(thread_list, thread_count);
		return KERN_FAILURE; 
	}

	NSLog(@"小罪ADD: set_hw_breakpoint: prepare to set breakpoint");

    kern_return_t kr_all = KERN_SUCCESS;
    //for (mach_msg_type_number_t i = 0; i < thread_count; i++) {
	for (mach_msg_type_number_t i = 0; i < 40; i++) {
        arm_debug_state64_t debug_state;
        mach_msg_type_number_t count = ARM_DEBUG_STATE64_COUNT;
        kern_return_t kr = thread_get_state(thread_list[i], ARM_DEBUG_STATE64,
                                            (thread_state_t)&debug_state, &count);
        if (kr != KERN_SUCCESS) { kr_all = kr; continue; }

        debug_state.__bvr[g_hwbp_index] = addr;
        debug_state.__bcr[g_hwbp_index] = (1ULL << 0) | (2ULL << 1) | (1ULL << 5); // 启用
        debug_state.__mdscr_el1 |= (1ULL << 15);   // 全局调试启用

        kr = thread_set_state(thread_list[i], ARM_DEBUG_STATE64,
                              (thread_state_t)&debug_state, count);
        if (kr != KERN_SUCCESS) kr_all = kr;
    }

    free_threads(thread_list, thread_count);
    pthread_mutex_unlock(&g_hwbp_mutex);
    return kr_all;
}

// 在所有线程上移除硬件断点
static kern_return_t remove_hw_breakpoint() {
    pthread_mutex_lock(&g_hwbp_mutex);
    mach_msg_type_number_t thread_count;
    thread_act_array_t thread_list = get_threads(&thread_count);
    if (!thread_list) { pthread_mutex_unlock(&g_hwbp_mutex); return KERN_FAILURE; }

    for (mach_msg_type_number_t i = 0; i < thread_count; i++) {
        arm_debug_state64_t debug_state;
        mach_msg_type_number_t count = ARM_DEBUG_STATE64_COUNT;
        if (thread_get_state(thread_list[i], ARM_DEBUG_STATE64,
                             (thread_state_t)&debug_state, &count) != KERN_SUCCESS)
            continue;
        debug_state.__bcr[g_hwbp_index] = 0; // 禁用断点
        thread_set_state(thread_list[i], ARM_DEBUG_STATE64,
                         (thread_state_t)&debug_state, count);
    }

    free_threads(thread_list, thread_count);
    pthread_mutex_unlock(&g_hwbp_mutex);
    return KERN_SUCCESS;
}



// 兼容访问 NEON 寄存器 __v 数组（通常成员名不变）
#define arm_neon_state64_get_v(neon, idx) ((neon).__v[idx])
#define arm_neon_state64_set_v(neon, idx, val) do { (neon).__v[idx] = (val); } while(0)

// 1. 补全必要定义
typedef struct {
    uint64_t dbgbvr[16]; // 断点值寄存器
    uint64_t dbgbcr[16]; // 断点控制寄存器
} arm64e_dbg_regs_t;

// 禁用/启用当前线程的硬件断点（核心原子操作）
static void toggle_hw_breakpoint(thread_t thread, int enable,uint64_t g_bp_addr) {
    if (g_bp_addr == 0 || thread == THREAD_NULL) return;
    
    arm64e_dbg_regs_t dbg_regs;
    mach_msg_type_number_t reg_count = sizeof(dbg_regs) / sizeof(uint64_t);
    
    // 读取调试寄存器
    kern_return_t kr = thread_get_state(thread, ARM_DEBUG_STATE64, (thread_state_t)&dbg_regs, &reg_count);
    if (kr != KERN_SUCCESS) return;

    // 找到匹配的断点槽位并切换状态
    for (int i = 0; i < 16; i++) {
        if (dbg_regs.dbgbvr[i] == g_bp_addr) {
            if (enable) {
                dbg_regs.dbgbcr[i] = 0x1; // 启用：执行断点
            } else {
                dbg_regs.dbgbcr[i] = 0x0; // 禁用
            }
            // 立即写回寄存器
            thread_set_state(thread, ARM_DEBUG_STATE64, (thread_state_t)&dbg_regs, reg_count);
            break;
        }
    }
}

static void setmypc(mach_port_t thread_port,uint64_t newpc)
{
		// 获取线程通用寄存器
		struct myARM_THREAD_STATE64 thread_state2;
        mach_msg_type_number_t thread_state_cnt = ARM_THREAD_STATE64_COUNT;
		kern_return_t kr = thread_get_state(thread_port, ARM_THREAD_STATE64,(thread_state_t)&thread_state2, &thread_state_cnt);
        if (kr != KERN_SUCCESS) {
            return;
        }
		uint64_t pc = thread_state2.__pc;

		NSLog(@"小罪ADD: setmypc: pc:%llx, newpc:%llx",pc,newpc);

		thread_state2.__pc = (uint64_t)newpc;
		thread_set_state(thread_port, ARM_THREAD_STATE64,(thread_state_t)&thread_state2, ARM_THREAD_STATE64_COUNT);
	

}

static void setmypcnew(mach_port_t thread_port,struct myARM_THREAD_STATE64 thread_state2)
{
		uint64_t pc = thread_state2.__pc;

		NSLog(@"小罪ADD: setmypcnew: thread_port:%llx, thread_state2.__pc:%llx",thread_port,thread_state2.__pc);

		thread_set_state(thread_port, ARM_THREAD_STATE64,(thread_state_t)&thread_state2, ARM_THREAD_STATE64_COUNT);
	

}

// 标记是否正在处理 SIGTRAP，防止重入
static volatile int g_is_handling_sigtrap = 0;

static pthread_mutex_t g_handler_mutex = PTHREAD_MUTEX_INITIALIZER;

// SIGTRAP 信号处理函数
static void sigtrap_handler(int signo, siginfo_t *info, void *context) {

	NSLog(@"小罪ADD: sigtrap_handler 触发！");
	
	// 防止信号重入（SIGTRAP 可能多次触发）
    if (g_is_handling_sigtrap || pthread_mutex_trylock(&g_handler_mutex) != 0) 
	{
        return;
    }
    
	
	
	// 安全校验：context 不能为空
    if (context == NULL) {
        NSLog(@"小罪ADD: context 为空，处理失败");
        g_is_handling_sigtrap = 0;
		pthread_mutex_unlock(&g_handler_mutex);
        return;
    }

	g_is_handling_sigtrap = 1;
	

	mach_port_t curr_thread = mach_thread_self();
	
	ucontext_t *uc = (ucontext_t *)context;
    arm_thread_state64_t *thread_state = &uc->uc_mcontext->__ss;
	arm_neon_state64_t *neon_state = &uc->uc_mcontext->__ns;

	struct myARM_THREAD_STATE64 *thread_state2 = (struct myARM_THREAD_STATE64 *)&uc->uc_mcontext->__ss;;
	
	//arm_thread_state64_t thread_state;
	//struct myARM_THREAD_STATE64 *thread_state2;
	
	// 使用兼容宏获取 PC
    uint64_t pc = arm_thread_state64_get_pc(*thread_state);
	NSLog(@"小罪ADD: sigtrap_handler: pc: 0x%llx, g_source_addr:0x%llx", pc, (uint64_t)g_source_addr);
    if (pc != g_source_addr) {
		NSLog(@"小罪ADD: sigtrap_handler : 不是我们设置的断点，忽略");
		thread_state2->__pc += 4;
		g_is_handling_sigtrap = 0;
		pthread_mutex_unlock(&g_handler_mutex);
        return; // 不是我们的断点
    }

	// 验证目标地址合法性（ARM64 指令必须 4 字节对齐）
    if (g_target_addr % 4 != 0) {
        NSLog(@"小罪ADD: 目标地址 0x%llx 未按 4 字节对齐，跳转失败", g_target_addr);
        thread_state2->__pc += 4; // 跳过断点指令
        g_is_handling_sigtrap = 0;
		pthread_mutex_unlock(&g_handler_mutex);
        return;
    }

	
	// ----- 获取并修改 NEON 浮点寄存器（s0, s1）-----
	float new_val = -0.01f;
    // 通过 union 或直接内存拷贝修改，确保不破坏高 96 位
    union {
        __uint128_t v;
        float f;
    } u0, u1;
	
    u0.v = arm_neon_state64_get_v(*neon_state, 0);
    u0.f = new_val;
    arm_neon_state64_set_v(*neon_state, 0, u0.v);
	
    u1.v = arm_neon_state64_get_v(*neon_state, 1);
    u1.f = new_val;
    arm_neon_state64_set_v(*neon_state, 1, u1.v);
	

	//arm_thread_state64_set_pc(*thread_state, (uint64_t)g_target_addr);  // 跳过当前指令
	//thread_state->__pc = (uint64_t)g_target_addr;
	//thread_state->pc = (uint64_t)g_target_addr;
	//arm_thread_state64_set_pc(*thread_state, (uint64_t)g_target_addr);

	// 1. 临时禁用断点（核心：避免返回后立刻触发）
    toggle_hw_breakpoint(curr_thread, 0,g_source_addr);

	// 2.修改pc 
	NSLog(@"小罪ADD: sigtrap_handler: 修改前的pc: 0x%llx", thread_state2->__pc);
	thread_state2->__pc = (uint64_t)g_target_addr;
	NSLog(@"小罪ADD: sigtrap_handler: 修改后的pc: 0x%llx", thread_state2->__pc);

	// 3. 立即恢复断点（保证下次还能触发）
    toggle_hw_breakpoint(curr_thread, 1,g_source_addr);

	//setmypc(curr_thread,g_target_addr);
	//setmypcnew(curr_thread,*thread_state2);

	// 重置标记
    g_is_handling_sigtrap = 0;
	pthread_mutex_unlock(&g_handler_mutex);
	//mach_port_deallocate(mach_task_self(), curr_thread);

	NSLog(@"小罪ADD: sigtrap_handler : 重置标记完成，进入下一环");
	//setmypcnew(curr_thread,*thread_state2);
	
	thread_state2->__pc += 4; 

}

	

typedef kern_return_t (*thread_get_state_t)(
    thread_act_t target_thread,
    thread_state_flavor_t flavor,
    thread_state_t old_state,
    mach_msg_type_number_t *old_stateCnt
);



static thread_get_state_t original_thread_get_state = NULL;

	
bool isover100 = false;

bool maindone = false;

// =============================================================================
// 设置指定索引的硬件断点 (在所有线程上)
// =============================================================================
static kern_return_t set_hw_breakpoint_at_index(int idx, mach_vm_address_t addr) {
    if (idx < 0 || idx >= MAX_HW_BREAKPOINTS)
        return KERN_INVALID_ARGUMENT;

    pthread_mutex_lock(&g_hwbp_mutex);
    mach_msg_type_number_t thread_count;
    thread_act_array_t thread_list = get_threads(&thread_count);
    if (!thread_list) {
        pthread_mutex_unlock(&g_hwbp_mutex);
        return KERN_FAILURE;
    }

	//NSLog(@"小罪ADD: set_hw_breakpoint_at_index: thread_count:%d",thread_count);

	/*
	while (thread_count < 40) 
	{ 
		
		
		//pthread_mutex_unlock(&g_hwbp_mutex); 
		free_threads(thread_list, thread_count);

		//sleep(5);
		thread_list = get_threads(&thread_count);
		//NSLog(@"小罪ADD: set_hw_breakpoint_at_index: thread_count:%d",thread_count);
		
		//return KERN_FAILURE; 
	}
	*/

	//NSLog(@"小罪ADD: set_hw_breakpoint_at_index: prepare to set breakpoint");

	//if(thread_count > 90)isover100 = true;

	//if(thread_count < 40) return KERN_FAILURE;

	//maindone = true;
	//NSLog(@"小罪ADD: set_hw_breakpoint_at_index: 有40个线程，prepare to set breakpoint");

	kern_return_t kr_all = KERN_SUCCESS;
    //for (mach_msg_type_number_t i = 0; i < thread_count; i++) {
	for (mach_msg_type_number_t i = 0; i < 40; i++) {

		/*
		if(addr == g_breakpoints[2].source)
		{
			if(i > 20) continue;
		}
		*/
		
        arm_debug_state64_t debug_state;
        mach_msg_type_number_t count = ARM_DEBUG_STATE64_COUNT;
        //kern_return_t kr = thread_get_state(thread_list[i], ARM_DEBUG_STATE64, (thread_state_t)&debug_state, &count);
		kern_return_t kr = original_thread_get_state(thread_list[i], ARM_DEBUG_STATE64, (thread_state_t)&debug_state, &count);
        if (kr != KERN_SUCCESS) { kr_all = kr; continue; }

        debug_state.__bvr[idx] = addr;
        debug_state.__bcr[idx] = (1ULL << 0) | (2ULL << 1) | (1ULL << 5); // 启用
        debug_state.__mdscr_el1 |= (1ULL << 15);   // 全局调试启用

        kr = thread_set_state(thread_list[i], ARM_DEBUG_STATE64,
                              (thread_state_t)&debug_state, count);
        if (kr != KERN_SUCCESS) kr_all = kr;
    }

    free_threads(thread_list, thread_count);
    pthread_mutex_unlock(&g_hwbp_mutex);
    return kr_all;
}

static kern_return_t set_hw_breakpoint_at_index_ter(int idx, mach_vm_address_t addr) {
    if (idx < 0 || idx >= MAX_HW_BREAKPOINTS)
	//if (idx < 0 || idx > 16)
        return KERN_INVALID_ARGUMENT;

    pthread_mutex_lock(&ter_hwbp_mutex);
    mach_msg_type_number_t thread_count;
    thread_act_array_t thread_list = get_threads(&thread_count);
    if (!thread_list) {
		//NSLog(@"小罪ADD: set_hw_breakpoint_at_index_ter: get thread_list fail!");
        pthread_mutex_unlock(&ter_hwbp_mutex);
        return KERN_FAILURE;
    }

	//NSLog(@"小罪ADD: set_hw_breakpoint_at_index_ter: thread_count:%d",thread_count);

	
	//if(thread_count < 41) return KERN_FAILURE;

	//if(thread_count > 90)isover100 = true;

    kern_return_t kr_all = KERN_SUCCESS;
    for (mach_msg_type_number_t i = 41; i < thread_count; i++) {
	//for (mach_msg_type_number_t i = 0; i < 40; i++) {
        arm_debug_state64_t debug_state;
        mach_msg_type_number_t count = ARM_DEBUG_STATE64_COUNT;
        //kern_return_t kr = thread_get_state(thread_list[i], ARM_DEBUG_STATE64,(thread_state_t)&debug_state, &count);
		kern_return_t kr = original_thread_get_state(thread_list[i], ARM_DEBUG_STATE64, (thread_state_t)&debug_state, &count);
        if (kr != KERN_SUCCESS) { kr_all = kr; continue; }

        debug_state.__bvr[idx] = addr;
        debug_state.__bcr[idx] = (1ULL << 0) | (2ULL << 1) | (1ULL << 5); // 启用
        debug_state.__mdscr_el1 |= (1ULL << 15);   // 全局调试启用

        kr = thread_set_state(thread_list[i], ARM_DEBUG_STATE64,(thread_state_t)&debug_state, count);
        if (kr != KERN_SUCCESS) kr_all = kr;
    }

    free_threads(thread_list, thread_count);
    pthread_mutex_unlock(&ter_hwbp_mutex);
    return kr_all;
}

bool TDMpaused =false;
bool mgpapaused =false;
bool cs2paused =false;
bool cs3paused =false;

void bianlixianchenghack()
{
	thread_act_array_t thread_list = NULL;
    mach_msg_type_number_t thread_count = 0;
    kern_return_t kr = 0;

    kr = task_threads(mach_task_self(), &thread_list, &thread_count);
    

    for (int i = 0; i < thread_count; i++) {
        
        mach_msg_type_number_t thread_info_count = THREAD_INFO_MAX;
        
        struct thread_extended_info thinfo ={};
        kr = thread_info(thread_list[i], THREAD_EXTENDED_INFO,
                         (thread_info_t)&thinfo, &thread_info_count);
        
        if (kr == KERN_SUCCESS)
        {	
			
            //if(strstr(thinfo.pth_name,"ace_cs2") || strstr(thinfo.pth_name,"ace_cs3"))

			if(!cs2paused)
			{
				if(strstr(thinfo.pth_name,"ace_cs2"))
	            {
	                kr = thread_suspend(thread_list[i]);
	                if (kr == KERN_SUCCESS)
	                {
	                    //kr = thread_abort_safely(thread_list[i]);
	                    NSLog(@"小罪ADD: thread_suspend: thread_list[i]:%d pth_name:%s",thread_list[i],thinfo.pth_name);
						cs2paused = true;
	                }
	                    //return true;
	            }
			}

			if(!cs3paused)
			{
				if(strstr(thinfo.pth_name,"ace_cs3"))
	            {
	                kr = thread_suspend(thread_list[i]);
	                if (kr == KERN_SUCCESS)
	                {
	                    //kr = thread_abort_safely(thread_list[i]);
	                    NSLog(@"小罪ADD: thread_suspend: thread_list[i]:%d pth_name:%s",thread_list[i],thinfo.pth_name);
						cs3paused = true;
	                }
	                    //return true;
	            }
			}
			

			/*
			if(!TDMpaused)
			{
				if(strstr(thinfo.pth_name,"TDM-report-1"))
	            {
	                kr = thread_suspend(thread_list[i]);
	                if (kr == KERN_SUCCESS)
	                {
	                    //kr = thread_abort_safely(thread_list[i]);
	                    NSLog(@"小罪ADD: thread_suspend: thread_list[i]:%d pth_name:%s",thread_list[i],thinfo.pth_name);
						TDMpaused = true;
	                }
	                    
	            }
			}
			*/
			

			
			if(!mgpapaused)
			{
				if(strstr(thinfo.pth_name,"mgpa"))
	            {
					
					 kr = thread_suspend(thread_list[i]);
	                if (kr == KERN_SUCCESS)
	                {
						NSLog(@"小罪ADD: thread_suspend: thread_list[i]:%d pth_name:%s",thread_list[i],thinfo.pth_name);
						mgpapaused = true;
					}
				}
			}
			
			
			
        }
        
    }

	if (thread_list != NULL) 
	{
   		 vm_deallocate(mach_task_self(), (vm_address_t)thread_list, thread_count * sizeof(thread_act_t));
	}
}

bool hadexchanged = false;

typedef uint64_t (*TssSDKOnPauseFunc)();
static TssSDKOnPauseFunc original_TssSDKOnPause = NULL;

typedef uint64_t (*TssSDKOnResumeFunc)();
static TssSDKOnResumeFunc original_TssSDKOnResume = NULL;

typedef uint64_t (*TssSDKFreeFunc)();
static TssSDKFreeFunc original_TssSDKFree = NULL;

static void ensurereporter()
{
	while(!tersafeadd)
	{
		tersafeadd = Get_tersafe_base();
	}

	while(!Imageaddress)
	{
		Imageaddress = Get_Imageaddress_base();
	}

	
	/*
	//uint64_t tersafereporter =  (uint64_t)(tersafeadd + 0x2B8210);
	uint64_t tersafereporter =  (uint64_t)(tersafeadd + 0x2B81E0);
	uint64_t retadd = (uint64_t)(tersafeadd + 0x88CC);//mov x0,#0
	if(retadd >0)
	{
		for(int i = 0;i < 26;i++)
		{	
			if((0x2B81E0 + i*8) == (0x2B8200))
			{
				uint64_t rd1 = (uint64_t)Read_Long(tersafereporter + i*8);
				uint64_t rd2 = (uint64_t)Read_Long(rd1+0x10);
				if( rd2 != retadd)
				{
					forcewritenewlong(rd1+0x10,(uint64_t)retadd);
					NSLog(@"小罪ADD: ensurereporter: tersafereporter: 0x%llx ,tersafeadd+ 0x88CC: 0x%llx,Read_Long(tersafereporter): 0x%llx", tersafereporter + i*8, retadd,rd2);
				}
				continue;
			}
	
			
			uint64_t rd = (uint64_t)Read_Long(tersafereporter + i*8);
			if( rd != retadd)
			{
				forcewritenewlong(tersafereporter + i*8,(uint64_t)retadd);
				NSLog(@"小罪ADD: ensurereporter: tersafereporter: 0x%llx ,tersafeadd+ 0x55B0: 0x%llx,Read_Long(tersafereporter): 0x%llx", tersafereporter, retadd,rd);
			}
			
			
		}
	}
	*/

	/*
	uint64_t rd = (uint64_t)Read_Long(tersafereporter);
	if( rd != retadd)
	{
		forcewritenewlong(tersafereporter,(uint64_t)retadd);
		NSLog(@"小罪ADD: ensurereporter: tersafereporter: 0x%llx ,tersafeadd+ 0x55B0: 0x%llx,Read_Long(tersafereporter): 0x%llx", tersafereporter, retadd,rd);
	}
	*/
	
	
	/*
	uint64_t huanjingjilu =  (uint64_t)(tersafeadd + 0x2E1D18);
	uint64_t rd2 = (uint64_t)Read_Long(huanjingjilu);
	if( rd2 != 0)
	{
		forcewritenewlong(huanjingjilu,0);
		NSLog(@"小罪ADD: ensurereporter: huanjingjilu: 0x%llx ,rd2: 0x%llx", huanjingjilu,rd2);

	}
	*/

	/*
	uint64_t huanjingchar =  (uint64_t)(tersafeadd + 0x2E0A68);
	char rd3 = (char)Read_Char(huanjingchar);
	if( rd3 != (char)1)
	{
		forcewritenewchar(huanjingchar,(char)1);
		NSLog(@"小罪ADD: ensurereporter: huanjingchar: 0x%llx ,rd3: %d,Read_Char(huanjingchar): %d", huanjingchar,rd3,Read_Char(huanjingchar));

	}
	*/

	/*
	uint64_t RMMemoryMonitorPluginadd = Imageaddress + 0x108EBBD0;
	uint64_t newadd = Imageaddress + 0x1A1C858;

	uint64_t RMMemoryMonitorPluginlong = (uint64_t)Read_Long(RMMemoryMonitorPluginadd);
	if(RMMemoryMonitorPluginlong != 0 &&  RMMemoryMonitorPluginlong !=  (uint64_t)(newadd))
	{
		forcewritenewlong(RMMemoryMonitorPluginadd,(uint64_t)newadd);
		NSLog(@"小罪ADD: ensurereporter: RMMemoryMonitorPluginadd: 0x%llx ,RMMemoryMonitorPluginlong: 0x%llx,Read_Long(RMMemoryMonitorPluginadd): 0x%llx", RMMemoryMonitorPluginadd, RMMemoryMonitorPluginlong,Read_Long(RMMemoryMonitorPluginadd));
	}
	*/

	
	uint64_t TssSDKOnPauseptr = Imageaddress + 0x103DE638;
	uint64_t TssSDKOnResumeptr = Imageaddress + 0x103DE650;

	//uint64_t TssSDKDelReportDataptr = Imageaddress + 0x103DE5F8;
	//uint64_t TssSDKDelReportData3ptr = Imageaddress + 0x103DE600;

	//uint64_t TssSDKFreeptr = Imageaddress + 0x103DE608;
	//uint64_t TssSDKOnPauseptr = Imageaddress + 0x103DE608; //伪装成free

	uint64_t TssSDKOnPauselong  = (uint64_t)Read_Long(TssSDKOnPauseptr);
	uint64_t TssSDKOnResumelong = (uint64_t)Read_Long(TssSDKOnResumeptr);

	if(TssSDKOnResumelong != 0 && TssSDKOnResumelong != TssSDKOnPauselong)
	//if(TssSDKOnResumelong != 0 && !hadexchanged)
	{
		forcewritenewlong(TssSDKOnResumeptr,(uint64_t)TssSDKOnPauselong);

		//forcewritenewlong(TssSDKDelReportDataptr,(uint64_t)TssSDKOnPauselong);
		//forcewritenewlong(TssSDKDelReportData3ptr,(uint64_t)TssSDKOnPauselong);
		
		//forcewritenewlong(TssSDKOnPauseptr,(uint64_t)TssSDKOnResumelong);//新增交换指针

		if(Read_Long(TssSDKOnResumeptr) == TssSDKOnPauselong)
		//&& Read_Long(TssSDKOnPauseptr) == TssSDKOnResumelong)
		{
			//hadexchanged = true;
			NSLog(@"小罪ADD: ensurereporter: TssSDKOnResumelong: 0x%llx ,TssSDKOnPauselong: 0x%llx,Read_Long(TssSDKOnResumeptr): 0x%llx", TssSDKOnResumelong, TssSDKOnPauselong,Read_Long(TssSDKOnResumeptr));
			//NSLog(@"小罪ADD: ensurereporter: TssSDKOnPauseptr: 0x%llx ,TssSDKOnPauselong: 0x%llx,Read_Long(TssSDKOnPauseptr): 0x%llx", TssSDKOnPauseptr, TssSDKOnPauselong,Read_Long(TssSDKOnPauseptr));

		}
		
		
	}

	//新写法
	uint64_t mainyouxizhuangtai1 =  (uint64_t)(Imageaddress + 0x146F112F);
	int mainyouxizhuangtai1count = Read_Int(mainyouxizhuangtai1);
	if( mainyouxizhuangtai1count != 1)
	{
		forcewritenew(mainyouxizhuangtai1,1);
		NSLog(@"小罪ADD: ensurereporter: mainyouxizhuangtai1: 0x%llx ,mainyouxizhuangtai1count: %d", mainyouxizhuangtai1,mainyouxizhuangtai1count);
	}

	//新写法
	uint64_t mainyouxizhuangtai2 =  (uint64_t)(Imageaddress + 0x14240830);
	int mainyouxizhuangtai2count = Read_Int(mainyouxizhuangtai2);
	if( mainyouxizhuangtai2count != 0)
	{
		forcewritenew(mainyouxizhuangtai2,0);
		NSLog(@"小罪ADD: ensurereporter: mainyouxizhuangtai2: 0x%llx ,mainyouxizhuangtai2count: %d", mainyouxizhuangtai2,mainyouxizhuangtai2count);
	}

	//新写法
	uint64_t mainyouxizhuangtai3 =  (uint64_t)(Imageaddress + 0x146F1130);
	int mainyouxizhuangtai3count = Read_Int(mainyouxizhuangtai3);
	if( mainyouxizhuangtai3count != 0)
	{
		forcewritenew(mainyouxizhuangtai3,0);
		NSLog(@"小罪ADD: ensurereporter: mainyouxizhuangtai3: 0x%llx ,mainyouxizhuangtai3count: %d", mainyouxizhuangtai3,mainyouxizhuangtai3count);
	}

	
	

	/*
	uint64_t TssSDKOnPausediaoyongptr = Imageaddress + 0xE3B4DC0;
	uint64_t TssSDKFreediaoyongptr = Imageaddress + 0xE3B4D78;

	if(Read_Long(TssSDKOnPausediaoyongptr) != 0 && Read_Long(TssSDKFreediaoyongptr) != 0 )
	{
		 original_TssSDKOnPause =(TssSDKOnPauseFunc)TssSDKOnPausediaoyongptr;

		 
		 //original_TssSDKFree = (TssSDKFreeFunc)TssSDKFreediaoyongptr;

		 original_TssSDKOnPause();
		 //original_TssSDKFree();
	
	}
	*/


	/*
	//TssSDKGetReportData2 count
	uint64_t TssSDKGetReportData2countptr =  (uint64_t)(tersafeadd + 0x2B8EC0);
	int count = (int)Read_Int(TssSDKGetReportData2countptr);
	if( count != 0)
	{
		forcewritenew(TssSDKGetReportData2countptr,0);
		NSLog(@"小罪ADD: ensurereporter: TssSDKGetReportData2countptr: 0x%llx ,count: %d", TssSDKGetReportData2countptr,count);
	}
	

	
	//TssSDKGetReportData2 count2
	uint64_t TssSDKGetReportData2count2ptr =  (uint64_t)(tersafeadd + 0x2B8E32);
	int count2 = (int)Read_Int(TssSDKGetReportData2count2ptr);
	if( count2 != 0)
	{
		forcewritenew(TssSDKGetReportData2count2ptr,0);
		NSLog(@"小罪ADD: ensurereporter: TssSDKGetReportData2count2ptr: 0x%llx ,count2: %d", TssSDKGetReportData2count2ptr,count2);
	}

	//TssSDKGetReportData2 count3
	uint64_t TssSDKGetReportData2count3ptr =  (uint64_t)(tersafeadd + 0x2B8EC4);
	int count3 = (int)Read_Int(TssSDKGetReportData2count3ptr);
	if( count3 != 0)
	{
		forcewritenew(TssSDKGetReportData2count3ptr,0);
		NSLog(@"小罪ADD: ensurereporter: TssSDKGetReportData2count3ptr: 0x%llx ,count2: %d", TssSDKGetReportData2count3ptr,count3);
	}
	*/

	
	uint64_t yueyuptr1 =  (uint64_t)(tersafeadd + 0x2B8D98);
	int yueyuptr1count = Read_Int(yueyuptr1);
	if( yueyuptr1count != 1)
	{
		forcewritenew(yueyuptr1,1);
		NSLog(@"小罪ADD: ensurereporter: yueyuptr1: 0x%llx ,yueyuptr1count: %d", yueyuptr1,yueyuptr1count);
	}

	uint64_t yueyuptr2=  (uint64_t)(tersafeadd + 0x2B7038);
	int yueyuptr2count = Read_Int(yueyuptr2);
	if( yueyuptr2count != 1)
	{
		forcewritenew(yueyuptr2,1);
		NSLog(@"小罪ADD: ensurereporter: yueyuptr2: 0x%llx ,yueyuptr2count: %d", yueyuptr2,yueyuptr2count);
	}

	uint64_t yueyuptr3=  (uint64_t)(tersafeadd + 0x2B7040);
	long yueyuptr3count = Read_Long(yueyuptr3);
	if( yueyuptr3count != 0)
	{
		forcewritenewlong(yueyuptr3,0);
		NSLog(@"小罪ADD: ensurereporter: yueyuptr3: 0x%llx ,yueyuptr3count: %lx", yueyuptr3,yueyuptr3count);
	}

	uint64_t yueyuptr4 =  (uint64_t)(tersafeadd + 0x2B8D98);
	int yueyuptr4count = Read_Int(yueyuptr4);
	if( yueyuptr4count != 1)
	{
		forcewritenew(yueyuptr4,1);
		NSLog(@"小罪ADD: ensurereporter: yueyuptr4: 0x%llx ,yueyuptr4count: %d", yueyuptr4,yueyuptr4count);
	}

	//bianlixianchenghack();
	

}

// =============================================================================
// 设置所有断点
// =============================================================================
static void setup_all_breakpoints(void) 
{

	if(!maindone)
	{
	    for (int i = 0; i < g_breakpoint_count; i++) {
			//NSLog(@"小罪ADD: setup_all_breakpoints: 准备设置 g_breakpoint g_breakpoint_count：%d",g_breakpoint_count);
	        if (!g_breakpoints[i].used) continue;
	        g_breakpoints[i].hw_index = i;   // 硬件索引与数组下标一致
	        kern_return_t kr = set_hw_breakpoint_at_index(i, g_breakpoints[i].source);
	        if (kr != KERN_SUCCESS) 
			{
	            //NSLog(@"小罪ADD: setup_all_breakpoints: Failed to set breakpoint %d at 0x%llx", i, g_breakpoints[i].source);
	        } else {
	            //NSLog(@"小罪ADD: setup_all_breakpoints: Breakpoint %d: 0x%llx -> 0x%llx (s0=%.3f, s1=%.3f)",i, g_breakpoints[i].source, g_breakpoints[i].target, g_breakpoints[i].s0_val, g_breakpoints[i].s1_val);
	        }
	    }
	}

	for (int n = 0; n < ter_breakpoint_count; n++) 
	{
		//NSLog(@"小罪ADD: setup_all_breakpoints: 准备设置 ter_breakpoint ter_breakpoint_count：%d",ter_breakpoint_count);
        if (!ter_breakpoints[n].used) continue;
        ter_breakpoints[n].hw_index = n;   // 硬件索引与数组下标一致
        kern_return_t kr = set_hw_breakpoint_at_index_ter(n, ter_breakpoints[n].source);
        if (kr != KERN_SUCCESS) 
		{
            //NSLog(@"小罪ADD: setup_all_breakpoints: Failed to set breakpoint %d at 0x%llx", i, ter_breakpoints[n].source);
        } else {
            //NSLog(@"小罪ADD: setup_all_breakpoints: Breakpoint %d: 0x%llx -> 0x%llx (s0=%.3f, s1=%.3f)",i, ter_breakpoints[n].source, ter_breakpoints[n].target, ter_breakpoints[n].s0_val, ter_breakpoints[n].s1_val);
        }
    }

	
}


// =============================================================================
// 移除指定索引的硬件断点（辅助函数）
// =============================================================================
static kern_return_t remove_hw_breakpoint_at_index(int idx) {
    if (idx < 0 || idx >= MAX_HW_BREAKPOINTS)
        return KERN_INVALID_ARGUMENT;

    pthread_mutex_lock(&g_hwbp_mutex);
    mach_msg_type_number_t thread_count;
    thread_act_array_t thread_list = get_threads(&thread_count);
    if (!thread_list) {
        pthread_mutex_unlock(&g_hwbp_mutex);
        return KERN_FAILURE;
    }

    for (mach_msg_type_number_t i = 0; i < thread_count; i++) {
        arm_debug_state64_t debug_state;
        mach_msg_type_number_t count = ARM_DEBUG_STATE64_COUNT;
        if (thread_get_state(thread_list[i], ARM_DEBUG_STATE64,
                             (thread_state_t)&debug_state, &count) != KERN_SUCCESS)
            continue;
        debug_state.__bcr[idx] = 0; // 禁用
        thread_set_state(thread_list[i], ARM_DEBUG_STATE64,
                         (thread_state_t)&debug_state, count);
    }

    free_threads(thread_list, thread_count);
    pthread_mutex_unlock(&g_hwbp_mutex);
    return KERN_SUCCESS;
}


// =============================================================================
// 移除所有断点
// =============================================================================
static void remove_all_breakpoints(void) {
    for (int i = 0; i < g_breakpoint_count; i++) {
        if (g_breakpoints[i].used && g_breakpoints[i].hw_index != -1) {
            remove_hw_breakpoint_at_index(g_breakpoints[i].hw_index);
            g_breakpoints[i].hw_index = -1;
        }
    }
}


// =============================================================================
// Mach 异常处理线程
// =============================================================================
static void* exception_handler_threadold(void* arg) {
    kern_return_t kr;
    mach_port_t task = mach_task_self();

    // 创建异常端口
    kr = mach_port_allocate(task, MACH_PORT_RIGHT_RECEIVE, &g_exception_port);
    while (kr != KERN_SUCCESS) {
        NSLog(@"小罪ADD: exception_handler_thread: Failed to allocate exception port");
		kr = mach_port_allocate(task, MACH_PORT_RIGHT_RECEIVE, &g_exception_port);
        return NULL;
    }

    kr = mach_port_insert_right(task, g_exception_port, g_exception_port,
                                MACH_MSG_TYPE_MAKE_SEND);
    while (kr != KERN_SUCCESS) {
		NSLog(@"小罪ADD: exception_handler_thread: Failed to mach_port_insert_right");
		kr = mach_port_insert_right(task, g_exception_port, g_exception_port,
                                MACH_MSG_TYPE_MAKE_SEND);
        //mach_port_destroy(task, g_exception_port);
        return NULL;
    }

    // 设置任务异常端口，只捕获 EXC_BREAKPOINT
    kr = task_set_exception_ports(task, EXC_MASK_BREAKPOINT, g_exception_port,
                                  EXCEPTION_DEFAULT | MACH_EXCEPTION_CODES,
                                  ARM_DEBUG_STATE64);
    while (kr != KERN_SUCCESS) {
		NSLog(@"小罪ADD: exception_handler_thread: Failed to task_set_exception_ports");
		kr = task_set_exception_ports(task, EXC_MASK_BREAKPOINT, g_exception_port,
                                  EXCEPTION_DEFAULT | MACH_EXCEPTION_CODES,
                                  ARM_DEBUG_STATE64);
        //mach_port_destroy(task, g_exception_port);
        return NULL;
    }

   NSLog(@"小罪ADD: exception_handler_thread: Mach exception handler installed, waiting for breakpoint at 0x%llx", g_source_addr);
	
    while (1) {
        struct {
            mach_msg_header_t head;
            mach_msg_body_t msgh_body;
            mach_msg_port_descriptor_t thread_port;
            mach_msg_port_descriptor_t task_port;
            NDR_record_t ndr;
            exception_type_t exception;
            mach_msg_type_number_t code_count;
            mach_exception_data_t code;
            char pad[512];
        } msg;

        kr = mach_msg(&msg.head, MACH_RCV_MSG, 0, sizeof(msg), g_exception_port,
                      MACH_MSG_TIMEOUT_NONE, MACH_PORT_NULL);
        if (kr != KERN_SUCCESS) {
            continue;
        }

        mach_port_t thread_port = msg.thread_port.name;
        exception_type_t exception = msg.exception;

        if (exception != EXC_BREAKPOINT) {
            mach_msg_destroy(&msg.head);
            continue;
        }

        // 获取线程通用寄存器状态
        arm_thread_state64_t thread_state;
		struct myARM_THREAD_STATE64 thread_state2;
        mach_msg_type_number_t thread_state_cnt = ARM_THREAD_STATE64_COUNT;
        //kr = thread_get_state(thread_port, ARM_THREAD_STATE64,(thread_state_t)&thread_state, &thread_state_cnt);
		kr = thread_get_state(thread_port, ARM_THREAD_STATE64,(thread_state_t)&thread_state2, &thread_state_cnt);
        if (kr != KERN_SUCCESS) {
            mach_msg_destroy(&msg.head);
            continue;
        }

        // 检查 PC 是否等于源地址
        //uint64_t pc = thread_state.__pc;  // 直接访问成员（arm_thread_state64_t 的 __pc 可用）
		//aaa.__pc == g_target_addr;
		//struct myARM_THREAD_STATE64 aaa = *(struct myARM_THREAD_STATE64 *)&thread_state;
		//uint64_t pc = aaa.__pc;
		uint64_t pc = thread_state2.__pc; 
		
        if (pc != g_source_addr) {
			NSLog(@"小罪ADD: exception_handler_thread: pc != g_source_addr ,pc:%llx",pc);
			
            // 不是我们的断点，忽略并继续
            // 但仍需回复 KERN_SUCCESS 让线程继续
            struct reply_msg {
                mach_msg_header_t head;
                NDR_record_t ndr;
                kern_return_t ret;
            } reply;
            reply.head.msgh_bits = MACH_MSGH_BITS(MACH_MSGH_BITS_REMOTE(msg.head.msgh_bits), 0);
            reply.head.msgh_size = sizeof(reply);
            reply.head.msgh_remote_port = msg.head.msgh_remote_port;
            reply.head.msgh_local_port = MACH_PORT_NULL;
            reply.head.msgh_id = msg.head.msgh_id + 100;
            reply.ndr = NDR_record;
            reply.ret = KERN_SUCCESS;
            mach_msg(&reply.head, MACH_SEND_MSG, reply.head.msgh_size, 0,
                     MACH_PORT_NULL, MACH_MSG_TIMEOUT_NONE, MACH_PORT_NULL);
            mach_msg_destroy(&msg.head);
            continue;
        }

		//NSLog(@"小罪ADD: exception_handler_thread: pc hit ! ,pc:%llx",pc);

        // ----- 获取并修改 NEON 浮点寄存器（s0, s1）-----
        arm_neon_state64_t neon_state;
        mach_msg_type_number_t neon_state_cnt = ARM_NEON_STATE64_COUNT;
        kr = thread_get_state(thread_port, ARM_NEON_STATE64,
                              (thread_state_t)&neon_state, &neon_state_cnt);
        if (kr == KERN_SUCCESS) {
            // s0 对应 v0 的低32位，s1 对应 v1 的低32位
            float new_s0 = -0.01f;
            float new_s1 = -0.01f;
            *(float*)&neon_state.__v[0] = new_s0;
            *(float*)&neon_state.__v[1] = new_s1;
            // 写回 NEON 状态
            thread_set_state(thread_port, ARM_NEON_STATE64,
                             (thread_state_t)&neon_state, neon_state_cnt);
        } else {
            // 无法获取 NEON 状态，继续但可能不会修改浮点寄存器
        }

        // ----- 修改 PC 为目标地址（持久跳转，不断开断点）-----
        //thread_state.__pc = (uint64_t)g_target_addr;
		thread_state2.__pc = (uint64_t)g_target_addr;
		//aaa.__pc == g_target_addr;
        //thread_set_state(thread_port, ARM_THREAD_STATE64,(thread_state_t)&thread_state, ARM_THREAD_STATE64_COUNT);
		thread_set_state(thread_port, ARM_THREAD_STATE64,(thread_state_t)&thread_state2, ARM_THREAD_STATE64_COUNT);

        // 注意：硬件断点未移除，因此下次执行到源地址时仍会触发

        // ----- 回复异常处理成功，让线程继续执行 -----
        struct reply_msg {
            mach_msg_header_t head;
            NDR_record_t ndr;
            kern_return_t ret;
        } reply;
        reply.head.msgh_bits = MACH_MSGH_BITS(MACH_MSGH_BITS_REMOTE(msg.head.msgh_bits), 0);
        reply.head.msgh_size = sizeof(reply);
        reply.head.msgh_remote_port = msg.head.msgh_remote_port;
        reply.head.msgh_local_port = MACH_PORT_NULL;
        reply.head.msgh_id = msg.head.msgh_id + 100;
        reply.ndr = NDR_record;
        reply.ret = KERN_SUCCESS;

        mach_msg(&reply.head, MACH_SEND_MSG, reply.head.msgh_size, 0,
                 MACH_PORT_NULL, MACH_MSG_TIMEOUT_NONE, MACH_PORT_NULL);

        mach_msg_destroy(&msg.head);
    }

    return NULL;
}

int bptype = -1;
int terbptype = -1;

static bool cached_flag128 = false; // false: 未缓存, true: 已缓存
static bool cached_flag576 = false; // false: 未缓存, true: 已缓存

static bool cached_flag160 = false; // false: 未缓存, true: 已缓存
static bool cached_flag400 = false; // false: 未缓存, true: 已缓存

static bool cached_flag1000 = false; // false: 未缓存, true: 已缓存


static uint8_t cached_struct128[128];
static uint8_t cached_struct576[576];

static uint8_t cached_struct160[160];
static uint8_t cached_struct400[400];

static uint8_t cached_struct1000[1000];

static void* exception_handler_thread_smoba(void* arg) 
{
	kern_return_t kr;
    mach_port_t task = mach_task_self();

    // 创建异常端口
    kr = mach_port_allocate(task, MACH_PORT_RIGHT_RECEIVE, &g_exception_port);
    while (kr != KERN_SUCCESS) {
        NSLog(@"小罪ADD: exception_handler_thread: Failed to allocate exception port");
		kr = mach_port_allocate(task, MACH_PORT_RIGHT_RECEIVE, &g_exception_port);
        return NULL;
    }

    kr = mach_port_insert_right(task, g_exception_port, g_exception_port,
                                MACH_MSG_TYPE_MAKE_SEND);
    while (kr != KERN_SUCCESS) {
		NSLog(@"小罪ADD: exception_handler_thread: Failed to mach_port_insert_right");
		kr = mach_port_insert_right(task, g_exception_port, g_exception_port,
                                MACH_MSG_TYPE_MAKE_SEND);
        //mach_port_destroy(task, g_exception_port);
        return NULL;
    }

    // 设置任务异常端口，只捕获 EXC_BREAKPOINT
    kr = task_set_exception_ports(task, EXC_MASK_BREAKPOINT, g_exception_port,
                                  EXCEPTION_DEFAULT | MACH_EXCEPTION_CODES,
                                  ARM_DEBUG_STATE64);
    while (kr != KERN_SUCCESS) {
		NSLog(@"小罪ADD: exception_handler_thread: Failed to task_set_exception_ports");
		kr = task_set_exception_ports(task, EXC_MASK_BREAKPOINT, g_exception_port,
                                  EXCEPTION_DEFAULT | MACH_EXCEPTION_CODES,
                                  ARM_DEBUG_STATE64);
        //mach_port_destroy(task, g_exception_port);
        return NULL;
    }

	//NSLog(@"小罪ADD: exception_handler_thread: 执行了mach_port_allocate \ mach_port_insert_right \task_set_exception_ports");

    NSLog(@"小罪ADD: exception_handler_thread: Mach exception handler started,g_breakpoint_count:%d,ter_breakpoint_count:%d",g_breakpoint_count,ter_breakpoint_count);

	
	//return NULL;

	
    while (1) {
        struct {
            mach_msg_header_t head;
            mach_msg_body_t msgh_body;
            mach_msg_port_descriptor_t thread_port;
            mach_msg_port_descriptor_t task_port;
            NDR_record_t ndr;
            exception_type_t exception;
            mach_msg_type_number_t code_count;
            mach_exception_data_t code;
            char pad[512];
        } msg;

        kr = mach_msg(&msg.head, MACH_RCV_MSG, 0, sizeof(msg), g_exception_port,
                      MACH_MSG_TIMEOUT_NONE, MACH_PORT_NULL);
        if (kr != KERN_SUCCESS) {
            continue;
        }

        mach_port_t thread_port = msg.thread_port.name;
        exception_type_t exception = msg.exception;

        if (exception != EXC_BREAKPOINT) {
            mach_msg_destroy(&msg.head);
            continue;
        }

		
        // 获取线程通用寄存器
        //arm_thread_state64_t thread_state;
		struct myARM_THREAD_STATE64 thread_state2;
        mach_msg_type_number_t thread_state_cnt = ARM_THREAD_STATE64_COUNT;
        //kr = thread_get_state(thread_port, ARM_THREAD_STATE64,(thread_state_t)&thread_state, &thread_state_cnt);
		kr = thread_get_state(thread_port, ARM_THREAD_STATE64,(thread_state_t)&thread_state2, &thread_state_cnt);
        if (kr != KERN_SUCCESS) {
            mach_msg_destroy(&msg.head);
            continue;
        }

        //uint64_t pc = arm_thread_state64_get_pc(thread_state);
		uint64_t pc = thread_state2.__pc; 

		bool istersafebp = false;

        // 查找匹配的断点
        Breakpoint *bp = NULL;
        //for (int i = 0; i < g_breakpoint_count; i++) 
		for (int i = 0; i < 16; i++) 
		{
            if (g_breakpoints[i].used && g_breakpoints[i].source == pc) 
			{
                bp = &g_breakpoints[i];
				bptype = i;
                break;
            }

			if (ter_breakpoints[i].used && ter_breakpoints[i].source == pc) 
			{
                bp = &ter_breakpoints[i];
				terbptype = i;
				istersafebp = true;
                break;
            }
			
        }

        if (!bp) {
            // 不是我们设置的断点，让线程继续
            goto send_reply;
        }

		if(istersafebp == false )
		{
			if(bptype == 0)
			{
				int myw8 = Read_Int((long)thread_state2.__x[19]);
				if(myw8 == 1)
				{
					thread_state2.__x[8] = 0;
					NSLog(@"小罪ADD: [开局写入add 0xA4E0FE0 hook] 主线程触发，myw8:%d准备修改为0",myw8);
				}
				else
				{
					thread_state2.__x[8] = myw8;
					NSLog(@"小罪ADD: [开局写入add 0xA4E0FE0 hook] 主线程触发，myw8:%d 不修改");
				}
				
				

			}

			if(bptype == 1)
			{
				//NSLog(@"小罪ADD: [sub_9AE9EF8 hook] 主线程触发 视距检测 返回0");
				NSLog(@"小罪ADD: [sub_A2337C8 hook] 主线程触发 视距检测 返回0");
			}

			if(bptype == 2)
			{
				NSLog(@"小罪ADD: [tersafe sub_6CF8 hook] 主线程触发"); //sub_6CF8 环境检测hook
			}

			if(bptype == 3)
			{
				//sub_210EAC ReportQueue_Enqueue
	
					uint64_t myptr = thread_state2.__x[1];
					int opcode = Read_Int(myptr);
					//const char* result = "";
					NSString *result = @"0";
	
					if(opcode < 0x100) result = @"小于0x100未的知异常";
					if(opcode >= 0x100 && opcode < 0x200) result = @"VM执行引擎异常、调试检测";
					if(opcode >= 0x200 && opcode < 0x300) result = @"Inline Hook / 代码完整性 / Session管理";
					if(opcode >= 0x300 && opcode < 0x400) result = @"VM opcode参数非法";
					if(opcode >= 0x400 && opcode < 0x500) result = @"VM opcode未知分支";
					if(opcode >= 0x500 && opcode < 0x600) result = @"定时器/调度系统异常";
					if(opcode >= 0x600 && opcode < 0x700) result = @"dladdr/内存映射异常";
					if(opcode >= 0x700 && opcode < 0x800) result = @"文件系统异常";
					if(opcode >= 0x800) result = @"超过0x800的未知异常";
	
					NSLog(@"小罪ADD: [tersafe sub_210EAC hook] ReportQueue_Enqueue 主线程 通道异常上报触发,opcode:%d,异常状态：%@",opcode,result);
					
			}

			if(bptype == 4)
			{
				NSLog(@"小罪ADD: [tersafe 0x2132C8 hook] 主线程调用 VM_DispatchPendingCallbacks");
			}

			if(bptype == 5)
			{
				NSLog(@"小罪ADD: [tersafe 0x93C10 hook] 主线程调用");
			}
			

		}

		if(istersafebp == true)
		{	
			if(terbptype == 0)
			{
				bool iscontainstr = false;
				//全局检测开关hook sub_AA880
				uint64_t path_ptr = thread_state2.__x[1];
			    char path[1024] = {0};
			    mach_vm_size_t bytes_read = 0;
			    kern_return_t kr = mach_vm_read_overwrite(mach_task_self(), path_ptr, sizeof(path)-1,
			                                              (mach_vm_address_t)path, &bytes_read);
			    if (kr == KERN_SUCCESS && bytes_read > 0) 
				{
			        path[bytes_read] = '\0';
			        //NSLog(@"小罪ADD: [tersafe 全局检测开关 sub_AA880 hook] 检测类型: %s", path);

					const char* result = "";

					result = strstr(path, "force");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "enc");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "hb");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "jb");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "jail");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "cs3");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "hook");
					if (result != NULL) iscontainstr = true;


					if(iscontainstr == true)
					{
						NSLog(@"小罪ADD: [tersafe 全局检测开关 sub_AA880 hook] tersafe线程 准备干掉字符串并返回0: %s", path);
						bp->target = (uint64_t)(hooked_ret0);
						//thread_state2.__sp -= 0x40;
						//bp->target = (uint64_t)(thread_state2.__pc + 4);
					}
					else
					{
						//NSLog(@"小罪ADD: [tersafe 全局检测开关 sub_AA880 hook] tersafe线程 暂时不干掉的检测类型: %s", path);
						thread_state2.__sp -= 0x40;
						bp->target = (uint64_t)(thread_state2.__pc + 4);
					}

					
			    } else 
				{
			        NSLog(@"小罪ADD: [tersafe 全局检测开关 sub_AA880 hook] tersafe线程 Failed to read 检测类型 at 0x%llx", path_ptr);
					// 模拟 SUB SP, SP, #0x40
					thread_state2.__sp -= 0x40;
					bp->target = (uint64_t)(thread_state2.__pc + 4);
			    }
				
			}

			if(terbptype == 1)
			{
				NSLog(@"小罪ADD: [tersafe sub_6CF8 hook] ter线程触发"); //sub_6CF8 环境检测hook
			}

			if(terbptype == 2)
			{
				//0x210EAC ReportQueue_Enqueue
	
					uint64_t myptr = thread_state2.__x[1];
					int opcode = Read_Int(myptr);
					//const char* result = "";
					NSString *result = @"0";
	
					if(opcode < 0x100) result = @"小于0x100未的知异常";
					if(opcode >= 0x100 && opcode < 0x200) result = @"VM执行引擎异常、调试检测";
					if(opcode >= 0x200 && opcode < 0x300) result = @"Inline Hook / 代码完整性 / Session管理";
					if(opcode >= 0x300 && opcode < 0x400) result = @"VM opcode参数非法";
					if(opcode >= 0x400 && opcode < 0x500) result = @"VM opcode未知分支";
					if(opcode >= 0x500 && opcode < 0x600) result = @"定时器/调度系统异常";
					if(opcode >= 0x600 && opcode < 0x700) result = @"dladdr/内存映射异常";
					if(opcode >= 0x700 && opcode < 0x800) result = @"文件系统异常";
					if(opcode >= 0x800) result = @"超过0x800的未知异常";
	
					NSLog(@"小罪ADD: [tersafe sub_210EAC hook] ReportQueue_Enqueue ter线程 通道异常上报触发,opcode:%d,异常状态：%@",opcode,result);
				
			}

			if(terbptype == 3)
			{
				//0x582A4 下发
				//sub_582A4 下发文件hook				
				uint64_t path_ptr = thread_state2.__x[0];
			    char path[1024] = {0};
			    mach_vm_size_t bytes_read = 0;
			    kern_return_t kr = mach_vm_read_overwrite(mach_task_self(), path_ptr, sizeof(path)-1,
			                                              (mach_vm_address_t)path, &bytes_read);
			    if (kr == KERN_SUCCESS && bytes_read > 0) {
			        path[bytes_read] = '\0';
			        NSLog(@"小罪ADD: [tersafe 王者 sub_582A4 hook] tersafe线程 下发Path: %s", path);
			    } else 
				{
			        //NSLog(@"小罪ADD: [tersafe 王者 sub_582A4 hook] tersafe线程 Failed to read path at 0x%llx", path_ptr);
			    }
			}

			if(terbptype == 4)
			{
				//0x2132C8 VM_DispatchPendingCallbacks
				NSLog(@"小罪ADD: [tersafe 0x2132C8 hook] ter调用 VM_DispatchPendingCallbacks");
			}

			if(terbptype == 5)
			{
				 //0x93C10 闪退
				 NSLog(@"小罪ADD: [tersafe 0x93C10 hook] ter线程调用");
			}

		}

		// 修改 PC 为目标地址（断点持续有效）
        //arm_thread_state64_set_pc(thread_state, bp->target);
		thread_state2.__pc = (uint64_t)bp->target;
        thread_set_state(thread_port, ARM_THREAD_STATE64,(thread_state_t)&thread_state2, ARM_THREAD_STATE64_COUNT);

    	send_reply:
        // 回复异常已处理
		{
	        struct {
	            mach_msg_header_t head;
	            NDR_record_t ndr;
	            kern_return_t ret;
	        } reply;
	        reply.head.msgh_bits = MACH_MSGH_BITS(MACH_MSGH_BITS_REMOTE(msg.head.msgh_bits), 0);
	        reply.head.msgh_size = sizeof(reply);
	        reply.head.msgh_remote_port = msg.head.msgh_remote_port;
	        reply.head.msgh_local_port = MACH_PORT_NULL;
	        reply.head.msgh_id = msg.head.msgh_id + 100;
	        reply.ndr = NDR_record;
	        reply.ret = KERN_SUCCESS;
	
	        mach_msg(&reply.head, MACH_SEND_MSG, reply.head.msgh_size, 0,
	                 MACH_PORT_NULL, MACH_MSG_TIMEOUT_NONE, MACH_PORT_NULL);
	
	        mach_msg_destroy(&msg.head);
		}

	}



}


static void* exception_handler_thread(void* arg) {
    kern_return_t kr;
    mach_port_t task = mach_task_self();

    // 创建异常端口
    kr = mach_port_allocate(task, MACH_PORT_RIGHT_RECEIVE, &g_exception_port);
    while (kr != KERN_SUCCESS) {
        NSLog(@"小罪ADD: exception_handler_thread: Failed to allocate exception port");
		kr = mach_port_allocate(task, MACH_PORT_RIGHT_RECEIVE, &g_exception_port);
        return NULL;
    }

    kr = mach_port_insert_right(task, g_exception_port, g_exception_port,
                                MACH_MSG_TYPE_MAKE_SEND);
    while (kr != KERN_SUCCESS) {
		NSLog(@"小罪ADD: exception_handler_thread: Failed to mach_port_insert_right");
		kr = mach_port_insert_right(task, g_exception_port, g_exception_port,
                                MACH_MSG_TYPE_MAKE_SEND);
        //mach_port_destroy(task, g_exception_port);
        return NULL;
    }

	//到这里都没拉闸
	

    // 设置任务异常端口，只捕获 EXC_BREAKPOINT
    kr = task_set_exception_ports(task, EXC_MASK_BREAKPOINT, g_exception_port,
                                  EXCEPTION_DEFAULT | MACH_EXCEPTION_CODES,
                                  ARM_DEBUG_STATE64);
    while (kr != KERN_SUCCESS) {
		NSLog(@"小罪ADD: exception_handler_thread: Failed to task_set_exception_ports");
		kr = task_set_exception_ports(task, EXC_MASK_BREAKPOINT, g_exception_port,
                                  EXCEPTION_DEFAULT | MACH_EXCEPTION_CODES,
                                  ARM_DEBUG_STATE64);
        //mach_port_destroy(task, g_exception_port);
        return NULL;
    }

	//NSLog(@"小罪ADD: exception_handler_thread: 执行了mach_port_allocate \ mach_port_insert_right \task_set_exception_ports");

    NSLog(@"小罪ADD: exception_handler_thread: Mach exception handler started,g_breakpoint_count:%d,ter_breakpoint_count:%d",g_breakpoint_count,ter_breakpoint_count);

	
	//return NULL;

	
    while (1) {
        struct {
            mach_msg_header_t head;
            mach_msg_body_t msgh_body;
            mach_msg_port_descriptor_t thread_port;
            mach_msg_port_descriptor_t task_port;
            NDR_record_t ndr;
            exception_type_t exception;
            mach_msg_type_number_t code_count;
            mach_exception_data_t code;
            char pad[512];
        } msg;

        kr = mach_msg(&msg.head, MACH_RCV_MSG, 0, sizeof(msg), g_exception_port,
                      MACH_MSG_TIMEOUT_NONE, MACH_PORT_NULL);
        if (kr != KERN_SUCCESS) {
            continue;
        }

        mach_port_t thread_port = msg.thread_port.name;
        exception_type_t exception = msg.exception;

        if (exception != EXC_BREAKPOINT) {
            mach_msg_destroy(&msg.head);
            continue;
        }

		/*
		// 获取线程通用寄存器状态
        arm_thread_state64_t thread_state;
		struct myARM_THREAD_STATE64 thread_state2;
        mach_msg_type_number_t thread_state_cnt = ARM_THREAD_STATE64_COUNT;
        //kr = thread_get_state(thread_port, ARM_THREAD_STATE64,(thread_state_t)&thread_state, &thread_state_cnt);
		kr = thread_get_state(thread_port, ARM_THREAD_STATE64,(thread_state_t)&thread_state2, &thread_state_cnt);
        if (kr != KERN_SUCCESS) {
            mach_msg_destroy(&msg.head);
            continue;
        }

        // 检查 PC 是否等于源地址
        //uint64_t pc = thread_state.__pc;  // 直接访问成员（arm_thread_state64_t 的 __pc 可用）
		//aaa.__pc == g_target_addr;
		//struct myARM_THREAD_STATE64 aaa = *(struct myARM_THREAD_STATE64 *)&thread_state;
		//uint64_t pc = aaa.__pc;
		uint64_t pc = thread_state2.__pc; 
		*/

        // 获取线程通用寄存器
        //arm_thread_state64_t thread_state;
		struct myARM_THREAD_STATE64 thread_state2;
        mach_msg_type_number_t thread_state_cnt = ARM_THREAD_STATE64_COUNT;
        //kr = thread_get_state(thread_port, ARM_THREAD_STATE64,(thread_state_t)&thread_state, &thread_state_cnt);
		kr = thread_get_state(thread_port, ARM_THREAD_STATE64,(thread_state_t)&thread_state2, &thread_state_cnt);
        if (kr != KERN_SUCCESS) {
            mach_msg_destroy(&msg.head);
            continue;
        }

        //uint64_t pc = arm_thread_state64_get_pc(thread_state);
		uint64_t pc = thread_state2.__pc; 

		bool istersafebp = false;

        // 查找匹配的断点
        Breakpoint *bp = NULL;
        //for (int i = 0; i < g_breakpoint_count; i++) 
		for (int i = 0; i < 16; i++) 
		{
            if (g_breakpoints[i].used && g_breakpoints[i].source == pc) 
			{
                bp = &g_breakpoints[i];
				bptype = i;
                break;
            }

			if (ter_breakpoints[i].used && ter_breakpoints[i].source == pc) 
			{
                bp = &ter_breakpoints[i];
				terbptype = i;
				istersafebp = true;
                break;
            }
			
        }

        if (!bp) {
            // 不是我们设置的断点，让线程继续
            goto send_reply;
        }

		/*
		if(istersafebp)
		{
			// 读取 stat 的第一个参数 (x0)
		    uint64_t path_ptr = thread_state2.__x[0];
		    char path[1024] = {0};
		    mach_vm_size_t bytes_read = 0;
		    kern_return_t kr = mach_vm_read_overwrite(mach_task_self(), path_ptr, sizeof(path)-1,
		                                              (mach_vm_address_t)path, &bytes_read);
		    if (kr == KERN_SUCCESS && bytes_read > 0) {
		        path[bytes_read] = '\0';
		        //NSLog(@"小罪ADD: [tersafe hook] Path: %s", path);
		    } else {
		        //NSLog(@"小罪ADD: [tersafe hook] Failed to read path at 0x%llx", path_ptr);
		    }

			thread_state2.__x[0] = 0;

		}
		else
		*/
		
		//if(istersafebp == false && bptype >= 0 //范围
		if(istersafebp == false )
		{
			if(bptype == 0 || bptype == 5)
			{	
				//NSLog(@"小罪ADD: 无后断点 触发");
		        // 修改浮点寄存器 s0/s1
		        arm_neon_state64_t neon_state;
		        mach_msg_type_number_t neon_cnt = ARM_NEON_STATE64_COUNT;
		        kr = thread_get_state(thread_port, ARM_NEON_STATE64,(thread_state_t)&neon_state, &neon_cnt);
		        if (kr == KERN_SUCCESS) 
				{
		            *(float*)&neon_state.__v[0] = bp->s0_val;
		            *(float*)&neon_state.__v[1] = bp->s1_val;
		            thread_set_state(thread_port, ARM_NEON_STATE64,(thread_state_t)&neon_state, neon_cnt);
		        }
			}

			if(bptype == 1)
			{	
				//0x801E5D8 shantuiadd3
				NSLog(@"小罪ADD: [主线程 0x801E5D8 hook] 主线程 shantuiadd3 返回0");
				
				//0x20FD6C 查询容器容量
				//NSLog(@"小罪ADD: [tersafe 0x20FD6C hook] 主线程 查询容器容量，返回0");

				//0x170278 全局游戏hook
				//NSLog(@"小罪ADD: [tersafe 0x170278 hook] 主线程调用 全局游戏hook");
				
				//sub_1081B241C DataFromTGPAcalladd
				//NSLog(@"小罪ADD: [sub_1081B241C hook] 主线程调用 DataFromTGPAcalladd检测 called!");
			
				//NSLog(@"小罪ADD: [tersafe 0xF6260 hook] 主线程调用 dwon检测");
				//NSLog(@"小罪ADD: [tersafe sub_6CF8 hook] 主线程触发");
			
				/*
				//0xAA880 检测控制开关
				bool iscontainstr = false;
				//全局检测开关hook sub_AA880
				uint64_t path_ptr = thread_state2.__x[1];
			    char path[1024] = {0};
			    mach_vm_size_t bytes_read = 0;
			    kern_return_t kr = mach_vm_read_overwrite(mach_task_self(), path_ptr, sizeof(path)-1,
			                                              (mach_vm_address_t)path, &bytes_read);
			    if (kr == KERN_SUCCESS && bytes_read > 0) 
				{
			        path[bytes_read] = '\0';
			        //NSLog(@"小罪ADD: [tersafe 全局检测开关 sub_AA880 hook] 检测类型: %s", path);

					const char* result = "";


					result = strstr(path, "force");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "enc");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "hb");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "jb");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "jail");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "cs3");
					if (result != NULL) iscontainstr = true;

					//////
					result = strstr(path, "scan");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "report");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "screenshot");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "process");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "dylib");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "900");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "module");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "hook");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "check");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "cert");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "IDFV");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "chk");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "jb");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "jail");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "tfp");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "hook");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "device");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "TDM");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "tdm");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "force");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "enc");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "hb");
					if (result != NULL) iscontainstr = true;

					//result = strstr(path, "Logout");
					//if (result != NULL) iscontainstr = true;


					
					//result = strstr(path, "mrpcs"); //会三方
					//if (result != NULL) iscontainstr = true;
					
					
					result = strstr(path, "anti");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "cs3");
					if (result != NULL) iscontainstr = true;

					//上面全部关闭也会三方
					
					
					
					result = strstr(path, "ts");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "tcj");
					if (result != NULL) iscontainstr = true;

					
					result = strstr(path, "gcloud");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "sc");
					if (result != NULL) iscontainstr = true;

					
					result = strstr(path, "dl");
					if (result != NULL) iscontainstr = true;
					

					
					//result = strstr(path, "mrmoni");  //会三方
					//if (result != NULL) iscontainstr = true;
					

					
					result = strstr(path, "sav");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "ac");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "ios");
					if (result != NULL) iscontainstr = true;
					
					result = strstr(path, "ob");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, ".img");
					if (result != NULL) iscontainstr = true;

					
					result = strstr(path, "filt");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "ne");
					if (result != NULL) iscontainstr = true;
					

					
					result = strstr(path, "mt");
					if (result != NULL) iscontainstr = true;

					

					
					result = strstr(path, "game");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "Game");
					if (result != NULL) iscontainstr = true;
					

					
					result = strstr(path, "ip");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "ds");
					if (result != NULL) iscontainstr = true;
					
					result = strstr(path, "port");
					if (result != NULL) iscontainstr = true;
					
					

					

					if(iscontainstr == true)
					{
						NSLog(@"小罪ADD: [tersafe 全局检测开关 sub_AA880 hook] 主线程 准备干掉字符串并返回0: %s", path);
						bp->target = (uint64_t)(hooked_ret0);
						//thread_state2.__sp -= 0x40;
						//bp->target = (uint64_t)(thread_state2.__pc + 4);
					}
					else
					{
						//NSLog(@"小罪ADD: [tersafe 全局检测开关 sub_AA880 hook] 主线程 暂时不干掉的检测类型: %s", path);
						thread_state2.__sp -= 0x40;
						bp->target = (uint64_t)(thread_state2.__pc + 4);
					}

					
			    } else 
				{
			        NSLog(@"小罪ADD: [tersafe 全局检测开关 sub_AA880 hook] 主线程 Failed to read 检测类型 at 0x%llx", path_ptr);
					// 模拟 SUB SP, SP, #0x40
					thread_state2.__sp -= 0x40;
					bp->target = (uint64_t)(thread_state2.__pc + 4);
			    }
				*/
			
				/*
				//0x2A2B0 _tp2_setuserinfo
				NSLog(@"小罪ADD: [tersafe 0x2A2B0 hook] _tp2_setuserinfo 主线程 called !");

				thread_state2.__x[0] = 3;

				//先还原
			    uint64_t sp = thread_state2.__sp;
				
			    //uint64_t new_x29 = sp + 0x50;
			    //thread_state2.__x[29] = new_x29;   // X29 即帧指针
				
				uint64_t new_x29 = sp + 0x50;
			    thread_state2.__fp = new_x29;   // 使用 __fp 而不是 __x[29]

				uint64_t open_id_ptr = thread_state2.__x[2];
			    char open_idpath1[1024] = {0};
			    mach_vm_size_t bytes_read1 = 0;
			    kern_return_t kr = mach_vm_read_overwrite(mach_task_self(), open_id_ptr, sizeof(open_idpath1)-1,
			                                              (mach_vm_address_t)open_idpath1, &bytes_read1);
				uint64_t role_id_ptr = thread_state2.__x[3];
			    char role_idpath2[1024] = {0};
			    mach_vm_size_t bytes_read2 = 0;
			    kr = mach_vm_read_overwrite(mach_task_self(), role_id_ptr, sizeof(role_idpath2)-1,
			                                              (mach_vm_address_t)role_idpath2, &bytes_read2);
	
			    if (kr == KERN_SUCCESS && bytes_read1 > 0 && bytes_read2 > 0) 
				{
			        open_idpath1[bytes_read1] = '\0';
					role_idpath2[bytes_read2] = '\0';
			        NSLog(@"小罪ADD: [tersafe 主线程 0x2A2B0 hook] 主线程触发 _tp2_setuserinfo open_id: %s ,role_id: %s",open_idpath1 , role_idpath2);

					//open_idpath1: 7916182520048297861

					if(open_idpath1)
					{
						const char *new_open_id   = "7916182520048297861";

						size_t write_len = strlen(new_open_id) + 1; // 19 + 1 = 20
				        kr = mach_vm_write(mach_task_self(), open_id_ptr, (mach_vm_address_t)new_open_id, write_len);
				        if (kr == KERN_SUCCESS) 
						{
							 kr = mach_vm_write(mach_task_self(), role_id_ptr, (mach_vm_address_t)new_open_id, write_len);
				             NSLog(@"小罪ADD: [tersafe 主线程 0x2A2B0 hook] 主线程触发 成功将 open_id 替换为 %s", new_open_id);
				        } else {
				            NSLog(@"小罪ADD: [tersafe 主线程 0x2A2B0 hook]  主线程触发 mach_vm_write 失败: %s", mach_error_string(kr));
				        }

					}

			    } 
				else 
				{
			        NSLog(@"小罪ADD: [tersafe 主线程 0x2A2B0 hook] 主线程触发 _tp2_setuserinfo Failed to read open_id at 0x%llx,role_id at 0x%llx,", open_id_ptr,role_id_ptr);
			    }
				*/

			
				/*
				//0x33DA4 tp2_setgamestatus
				uint64_t a1 = thread_state2.__x[0];
				NSLog(@"小罪ADD: [tersafe 0x33DA4 hook] 主线程触发 tp2_setgamestatus a2:%d",a1); 

				if(a1 == 1)// || a2 == 3
				{
					thread_state2.__x[1] = 2;
					//bp->target = (uint64_t)(hooked_ret0);
					NSLog(@"小罪ADD: [tersafe 0x33DA4 hook] 主线程触发 TssSDKOnResume 触发：a1:%d改为:%d",a1,thread_state2.__x[1]);
					thread_state2.__sp = thread_state2.__sp - 0x20;
					bp->target = (uint64_t)(tersafeadd + 0x33DA8);
				}
				else
				{
					NSLog(@"小罪ADD: [tersafe 0x33DA4 hook] 主线程触发 TssSDKOnPause 触发，放行");
					thread_state2.__sp = thread_state2.__sp - 0x20;
					bp->target = (uint64_t)(tersafeadd + 0x33DA8);
				}
				*/

				/*
				//0x3F744 TssSDKDispatchMonitorEvent
				uint64_t a2 = thread_state2.__x[1];
				NSLog(@"小罪ADD: [tersafe 0x3F744 hook] 主线程触发TssSDKDispatchMonitorEvent a2:%d,直接返回0",a2); 
				*/
				
				/*
				if(a2 == 2)// || a2 == 3
				{
					thread_state2.__x[1] = 3;
					//bp->target = (uint64_t)(hooked_ret0);
					NSLog(@"小罪ADD: [tersafe 0x3F744 hook] 主线程触发TssSDKDispatchMonitorEvent TssSDKOnPause触发：a2:%d改为:%d",a2,thread_state2.__x[1]);
					thread_state2.__sp = thread_state2.__sp - 0x30;
					bp->target = (uint64_t)(tersafeadd + 0x3F748);
				}
				else
				{
					thread_state2.__sp = thread_state2.__sp - 0x30;
					bp->target = (uint64_t)(tersafeadd + 0x3F748);
				}
				*/
			
				//0x154108 commit_patch_memory
				//NSLog(@"小罪ADD: [tersafe 0x154108 hook] 主线程触发commit_patch_memory"); 
				//NSLog(@"小罪ADD: [tersafe sub_6CF8 hook] 主线程触发");
				//NSLog(@"小罪ADD: [tersafe sub_24B47C hook] 主线程触发 VM_DebugDetect_Dispatch");
				//NSLog(@"小罪ADD: [tersafe sub_24B47C hook] 主线程触发 VM_DebugDetect_Dispatch");

				/*
				// 上报警告检测hook sub_824AC
				uint64_t path_ptr = thread_state2.__x[1];
			    char path[1024] = {0};
			    mach_vm_size_t bytes_read = 0;
			    kern_return_t kr = mach_vm_read_overwrite(mach_task_self(), path_ptr, sizeof(path)-1,
			                                              (mach_vm_address_t)path, &bytes_read);
			    if (kr == KERN_SUCCESS && bytes_read > 0) 
				{
			        path[bytes_read] = '\0';
			        NSLog(@"小罪ADD: [tersafe 主线程 警告上报sub_824AC hook] 检测类型: %s", path);

					
			    } else 
				{
			        NSLog(@"小罪ADD: [tersafe 主线程 警告上报sub_824AC hook] Failed to read 检测类型 at 0x%llx", path_ptr);
			    }
				*/
				
				
			}

			if(bptype == 2) 
			{	
				//0x210330 范围上报检测
				//NSLog(@"小罪ADD: [tersafe 0x210330 hook] 主线程触发 范围上报检测");
			
				//NSLog(@"小罪ADD: [tersafe 0x939A4 hook] ter线程触发 ScanEngine_GetInstance");
				
				/*
				//NSLog(@"小罪ADD: [tersafe 0x97C68 hook] 主线程触发 EventReport_Dispatch,a1:%d",a1);
				uint64_t a1 = thread_state2.__x[0];
				uint64_t path_ptr = thread_state2.__x[1];
			    char path[1024] = {0};
			    mach_vm_size_t bytes_read = 0;
			    kern_return_t kr = mach_vm_read_overwrite(mach_task_self(), path_ptr, sizeof(path)-1,
			                                              (mach_vm_address_t)path, &bytes_read);
			    if (kr == KERN_SUCCESS && bytes_read > 0) 
				{
			        path[bytes_read] = '\0';
			        NSLog(@"小罪ADD: [tersafe 主线程 0x97C68 hook] 主线程触发 EventReport_Dispatch,a1:%d,检测类型: %s",a1,path);

					
			    } else 
				{
			        NSLog(@"小罪ADD: [tersafe 主线程 0x97C68 hook] Failed to read 检测类型 at 0x%llx,a1:%d", path_ptr,a1);
			    }
				*/


				//NSLog(@"小罪ADD: [主程序 sub_10124DA40 hook] 主线程触发");
				
				
				//0x218D58 hook
					//sub_210330 hook 
					//0x21033C hook
				int a2 = thread_state2.__x[1];

				int v2 = Read_Int(thread_state2.__x[0] + 0x10) + 1;

				int biaoshi = Read_Int(thread_state2.__x[0] + 0x14);

				int shujusize = Read_Int(thread_state2.__x[0] + 0x18);

				
				if(shujusize == 128 || shujusize == 576 || shujusize == 160 || shujusize == 400 || shujusize == 1000 )// 
				{
					NSLog(@"小罪ADD: [tersafe 0x21033C hook] 主线程范围检测触发（sub_210330 RingBuf_Tick),a2 = %d,v2 = %d,biaoshi = %d,shujusize = %d",a2,v2,biaoshi,shujusize);

					if (shujusize == 128) 
					{
						if (!cached_flag128) 
						{
							// 首次出现128字节，缓存
				            memcpy((void *)cached_struct128, (void *)thread_state2.__x[0], 128);
				            cached_flag128 = true;
							NSLog(@"小罪ADD: [tersafe 0x218D58 hook] 主线程范围检测触发 128首次出现，已记录");
						}
						else
						{
							memcpy((void *)thread_state2.__x[0], (void *)cached_struct128, 128);
							//memcpy((void *)(thread_state2.__x[0]+64), (void *)cached_struct128, 64);
							NSLog(@"小罪ADD: [tersafe 0x218D58 hook] 主线程范围检测触发 128出现，已替换");
						}
					}

					if (shujusize == 576) 
					{
						if (!cached_flag576) 
						{
							// 首次出现128字节，缓存
				            memcpy((void *)cached_struct576, (void *)thread_state2.__x[0], 576);
				            cached_flag576 = true;
							NSLog(@"小罪ADD: [tersafe 0x218D58 hook] 主线程范围检测触发 576首次出现，已记录");
						}
						else
						{
							memcpy((void *)thread_state2.__x[0], (void *)cached_struct576, 576);
							//memcpy((void *)thread_state2.__x[0], (void *)cached_struct576, 64);
							//memcpy((void *)(thread_state2.__x[0]+288), (void *)cached_struct576, 288);
							NSLog(@"小罪ADD: [tersafe 0x218D58 hook] 主线程范围检测触发 576出现，已替换");
						}
					}

					if (shujusize == 160) 
					{
						if (!cached_flag160) 
						{
							// 首次出现 160 字节，缓存
				            memcpy((void *)cached_struct160, (void *)thread_state2.__x[0], 160);
				            cached_flag160 = true;
							NSLog(@"小罪ADD: [tersafe 0x218D58 hook] 主线程范围检测触发 160 首次出现，已记录");
						}
						else
						{
							memcpy((void *)thread_state2.__x[0], (void *)cached_struct160, 160);
							//memcpy((void *)thread_state2.__x[0], (void *)cached_struct160, 64);
							//memcpy((void *)(thread_state2.__x[0]+80), (void *)cached_struct160, 80);
							NSLog(@"小罪ADD: [tersafe 0x218D58 hook] 主线程范围检测触发 160 出现，已替换");
						}
					}

					if (shujusize == 400) 
					{
						if (!cached_flag400) 
						{
							// 首次出现 400 字节，缓存
				            memcpy((void *)cached_struct400, (void *)thread_state2.__x[0], 400);
				            cached_flag160 = true;
							NSLog(@"小罪ADD: [tersafe 0x218D58 hook] 主线程范围检测触发 400 首次出现，已记录");
						}
						else
						{
							memcpy((void *)thread_state2.__x[0], (void *)cached_struct400, 400);
							//memcpy((void *)thread_state2.__x[0], (void *)cached_struct400, 64);
							//memcpy((void *)(thread_state2.__x[0]+200), (void *)cached_struct400, 200);
							NSLog(@"小罪ADD: [tersafe 0x218D58 hook] 主线程范围检测触发 400 出现，已替换");
						}
					}

					if (shujusize == 1000) 
					{
						if (!cached_flag1000) 
						{
							// 首次出现 1000 字节，缓存
				            memcpy((void *)cached_struct1000, (void *)thread_state2.__x[0], 1000);
				            cached_flag1000 = true;
							NSLog(@"小罪ADD: [tersafe 0x218D58 hook] 主线程范围检测触发 1000 首次出现，已记录");
						}
						else
						{
							memcpy((void *)thread_state2.__x[0], (void *)cached_struct1000, 1000);
							//vm_copy(mach_task_self(), (vm_address_t)cached_struct1000, 1000, (vm_address_t)thread_state2.__x[0]);
							//memcpy((void *)thread_state2.__x[0], (void *)cached_struct1000, 64);
							//memcpy((void *)(thread_state2.__x[0]+100), (void *)cached_struct1000, 200);
							NSLog(@"小罪ADD: [tersafe 0x218D58 hook] 主线程范围检测触发 1000 出现，已替换");
						}
					}

					//old
					thread_state2.__lr = (uint64_t)(tersafeadd + 0x218D5C);
					bp->target = (uint64_t)(tersafeadd + 0x210330);

					
					
				}
				else
				{
					NSLog(@"小罪ADD: [tersafe 0x218D58 hook] 主线程范围检测触发放行(非576或128)（sub_210330 RingBuf_Tick),a2 = %d,v2 = %d,biaoshi = %d,shujusize = %d",a2,v2,biaoshi,shujusize);

					thread_state2.__lr = (uint64_t)(tersafeadd + 0x218D5C);
					bp->target = (uint64_t)(tersafeadd + 0x210330);
				
				}
				

			}

			if(bptype == 3) //异常上报ReportQueue_Enqueue sub_210EAC
			{
				//0x20FCF4 ReportQueue_Enqueue write
				//NSLog(@"小罪ADD: [tersafe 0x20FCF4 hook] 主线程 ReportQueue_Enqueue write called");

			
					
					uint64_t myptr = thread_state2.__x[1];
					int opcode = Read_Int(myptr);
					//const char* result = "";
					NSString *result = @"0";
	
					if(opcode < 0x100) result = @"小于0x100未的知异常";
					if(opcode >= 0x100 && opcode < 0x200) result = @"VM执行引擎异常、调试检测";
					if(opcode >= 0x200 && opcode < 0x300) result = @"Inline Hook / 代码完整性 / Session管理";
					if(opcode >= 0x300 && opcode < 0x400) result = @"VM opcode参数非法";
					if(opcode >= 0x400 && opcode < 0x500) result = @"VM opcode未知分支";
					if(opcode >= 0x500 && opcode < 0x600) result = @"定时器/调度系统异常";
					if(opcode >= 0x600 && opcode < 0x700) result = @"dladdr/内存映射异常";
					if(opcode >= 0x700 && opcode < 0x800) result = @"文件系统异常";
					if(opcode >= 0x800) result = @"超过0x800的未知异常";
	
					NSLog(@"小罪ADD: [tersafe sub_210EAC hook] ReportQueue_Enqueue 主线程 通道异常上报触发,opcode:%d,异常状态：%@",opcode,result);
					
	
			}

			if(bptype== 4)
			{
				//0x1AEB30 自瞄hook
				//NSLog(@"小罪ADD: [tersafe 0x1AEB30 hook] 主线程触发 自瞄hook检测"); 
				
				//0x821F948 shantuiadd2
				//NSLog(@"小罪ADD: [主程序 0x821F948 hook] 主线程触发 shantuiadd2"); 
				
				//0xC4086C4 DataFromTGPAadd2
				//NSLog(@"小罪ADD: [0xC4086C4 hook] 主线程触发 DataFromTGPAadd2 检测");
				
				//0xA4DE4 nj
				//NSLog(@"小罪ADD: [tersafe 0xA4DE4 hook] tersafe触发 nj检测"); //0xA4DE4 nj检测
			
			
				//NSLog(@"小罪ADD: [tersafe 0x20F42C hook] 主线程调用 NetObj_GetInstance");
			

				
				//thread_state2.__x[0] = tersafeadd + 0x2B8E32;
				
				//NSLog(@"小罪ADD: [tersafe 0x2B2AC hook] 主线程调用 tss_get_report_data2");

				//NSLog(@"小罪ADD: [主程序 sub_107A120BC hook] 主线程调用 游戏内置Hook");

			
				//NSLog(@"小罪ADD: [tersafe 0x193F90 hook] 主线程调用 游戏内置Hook");
				
				//NSLog(@"小罪ADD: [tersafe sub_241968(BufWriter_WriteField) hook] 主线程调用");
				
				
			
			}

			//if(bptype == 5)
			{
				
				

				//uint64_t a2 = thread_state2.__x[1];
				//NSLog(@"小罪ADD: [tersafe 0x2412D0 BufWriter_Init hook] 主线程触发,a2:%d",a2);
				
			}



			
		}
		
		

		if(istersafebp == true)
		{
			
			if(terbptype == 0) 
			{	
				//0x801E5F4 shantuiadd3
				NSLog(@"小罪ADD: [ter线程 0x801E5F4 hook] 主线程 shantuiadd3 返回0");
				
				//0x170278 全局游戏hook
				//NSLog(@"小罪ADD: [tersafe 0x170278 hook] ter线程调用 全局游戏hook");
				
				//0xF6260 down 
				//NSLog(@"小罪ADD: [tersafe 0xF6260 hook] ter线程调用 dwon检测");

				
				
			
				//0x20FD6C 查询容器容量
				//NSLog(@"小罪ADD: [tersafe 0x20FD6C hook] ter线程 查询容器容量，返回0");
			
				//NSLog(@"小罪ADD: [tersafe 0x2103B8 hook] 新写法防闪退");


				/*
				//sub_582A4 下发文件hook				
				uint64_t path_ptr = thread_state2.__x[0];
			    char path[1024] = {0};
			    mach_vm_size_t bytes_read = 0;
			    kern_return_t kr = mach_vm_read_overwrite(mach_task_self(), path_ptr, sizeof(path)-1,
			                                              (mach_vm_address_t)path, &bytes_read);
			    if (kr == KERN_SUCCESS && bytes_read > 0) {
			        path[bytes_read] = '\0';
			        NSLog(@"小罪ADD: [tersafe 三角洲 sub_582A4 或王者0x57B58 hook] tersafe线程 Path: %s", path);
			    } else 
				{
			        //NSLog(@"小罪ADD: [tersafe 三角 sub_582A4 或王者0x57B58 hook] tersafe线程 Failed to read path at 0x%llx", path_ptr);
			    }
				*/
				
				
				//NSLog(@"小罪ADD: [tersafe 0x939A4 hook] ter线程触发 ScanEngine_GetInstance");

				/*
				//NSLog(@"小罪ADD: [tersafe 0x97C68 hook] ter线程触发 EventReport_Dispatch,a1:%d",a1);
				uint64_t a1 = thread_state2.__x[0];
				uint64_t path_ptr = thread_state2.__x[1];
			    char path[1024] = {0};
			    mach_vm_size_t bytes_read = 0;
			    kern_return_t kr = mach_vm_read_overwrite(mach_task_self(), path_ptr, sizeof(path)-1,
			                                              (mach_vm_address_t)path, &bytes_read);
			    if (kr == KERN_SUCCESS && bytes_read > 0) 
				{
			        path[bytes_read] = '\0';
			        NSLog(@"小罪ADD: [tersafe 0x97C68 hook] ter线程触发 EventReport_Dispatch,a1:%d,检测类型: %s",a1,path);

					
			    } else 
				{
			        NSLog(@"小罪ADD: [tersafe 0x97C68 hook] ter线程触发 Failed to read 检测类型 at 0x%llx,a1:%d", path_ptr,a1);
			    }
				*/
				
				//NSLog(@"小罪ADD: [tersafe 0x254818 hook] tersafe模块 VM_DebugDetect_Instance2 触发");
				
				
				
				
			}

			
			if(terbptype == 1) 
			{
				//NSLog(@"小罪ADD: [tersafe 0x2132C8 hook] ter调用 VM_DispatchPendingCallbacks");
				
				//NSLog(@"小罪ADD: [tersafe sub_24B47C(VM_DebugDetect_Dispatch) hook] tersafe触发"); 
				
				/*
				uint64_t a3  = thread_state2.__x[2];
				if(a3 < 100)
				{
					// 模拟 SUB SP, SP, #0x60
				    thread_state2.__sp -= 0x60;
				    // 跳过当前指令
				    //thread_state2.__pc += 4;
					bp->target = (uint64_t)(thread_state2.__pc + 4);
				}
				else
				{
					bp->target = (uint64_t)(hooked_sub241578);
				}
				*/

				

				//NSLog(@"小罪ADD: [mach异常： 三角洲hooked_sub241578 hook] 命中！");
				/*
				bool istargetadd = false;
				uint64_t pc = thread_state2.__pc;
				uint64_t lr = thread_state2.__lr;
				uint64_t fp = thread_state2.__fp;   // x29
				uint64_t sp = thread_state2.__sp;

				int depth = 0;
				uint64_t current_fp = fp;
				while (current_fp != 0 && depth < 5) { // 限制最大深度，避免无限循环
				    uint64_t next_fp = 0;
				    uint64_t ret_addr = 0;
				    mach_vm_size_t bytes_read = 0;
				
				    // 读取 [current_fp] 处的前一个 FP
				    kr = mach_vm_read_overwrite(mach_task_self(), current_fp, sizeof(next_fp),
				                                (mach_vm_address_t)&next_fp, &bytes_read);
				    if (kr != KERN_SUCCESS || bytes_read != sizeof(next_fp)) {
				        //NSLog(@"小罪ADD: [mach异常： 三角洲hooked_sub241578 hook] Failed to read next FP at 0x%llx", current_fp);
				        break;
				    }
				
				    // 读取 [current_fp + 8] 处的返回地址
				    kr = mach_vm_read_overwrite(mach_task_self(), current_fp + 8, sizeof(ret_addr),
				                                (mach_vm_address_t)&ret_addr, &bytes_read);
				    if (kr != KERN_SUCCESS || bytes_read != sizeof(ret_addr)) {
				        //NSLog(@"小罪ADD: [mach异常： 三角洲hooked_sub241578 hook] Failed to read return address at 0x%llx", current_fp + 8);
				        break;
				    }
				
				    //NSLog(@"小罪ADD: [mach异常： 三角洲hooked_sub241578 hook] Frame %d: FP=0x%llx, Return Address=0x%llx", depth, current_fp, ret_addr);
				    if(ret_addr == (uint64_t)(tersafeadd + 0x218D5C))
					{
						NSLog(@"小罪ADD: [mach异常： 三角洲hooked_sub241578 hook] Frame %d: FP=0x%llx, Return Address=0x%llx,ptr:0x%llx", depth, current_fp, ret_addr,ret_addr - tersafeadd);
						istargetadd = true;
						break;
					}
					
					current_fp = next_fp;
				    depth++;
				}

				uint64_t a3  = thread_state2.__x[2];


				if(!istargetadd)
				{
					bp->target = (uint64_t)(hooked_sub241578);
					kern_return_t kr = thread_suspend(thread_port);
					if (kr == KERN_SUCCESS) {
					    NSLog(@"小罪ADD: Thread 0x%x suspended at breakpoint", thread_port);
					} else {
					    NSLog(@"小罪ADD: Failed to suspend thread: %s", mach_error_string(kr));
					}
				}
				else
				{
					// 模拟 SUB SP, SP, #0x60
				    thread_state2.__sp -= 0x60;
				    // 跳过当前指令
				    //thread_state2.__pc += 4;
					bp->target = (uint64_t)(thread_state2.__pc + 4);
				}
				*/
				
				
			}

			if(terbptype == 2) 
			{
				//0x20F42C NetObj_GetInstance
				//NSLog(@"小罪ADD: [tersafe 0x20F42C hook] ter线程调用 NetObj_GetInstance");
	
				//0x1AEB30 自瞄hook
				//NSLog(@"小罪ADD: [tersafe 0x1AEB30 hook] tersafe触发 自瞄hook检测"); 
				
				//0xA4DE4 nj
				//NSLog(@"小罪ADD: [tersafe 0xA4DE4 hook] tersafe触发 nj检测"); //0xA4DE4 nj检测
				
				//NSLog(@"小罪ADD: [tersafe sub_6CF8 hook] tersafe触发"); //sub_6CF8 环境检测hook
	
				/*
				//0x218D58 hook
				//sub_210330 hook
				//
				int a2 = thread_state2.__x[1];

				int v2 = Read_Int(thread_state2.__x[0] + 0x10) + 1;

				int biaoshi = Read_Int(thread_state2.__x[0] + 0x14);

				int shujusize = Read_Int(thread_state2.__x[0] + 0x18);

				
				if(shujusize == 128 || shujusize == 576 || shujusize == 160 || shujusize == 400 || shujusize == 1000 )// 
				{
					NSLog(@"小罪ADD: [tersafe 0x218D58 hook] ter线程范围检测触发（sub_210330 RingBuf_Tick),a2 = %d,v2 = %d,biaoshi = %d,shujusize = %d",a2,v2,biaoshi,shujusize);

					if (shujusize == 128) 
					{
						if (!cached_flag128) 
						{
							// 首次出现128字节，缓存
				            memcpy((void *)cached_struct128, (void *)thread_state2.__x[0], 128);
				            cached_flag128 = true;
							NSLog(@"小罪ADD: [tersafe 0x218D58 hook] ter线程范围检测触发 128首次出现，已记录");
						}
						else
						{
							memcpy((void *)thread_state2.__x[0], (void *)cached_struct128, 128);
							NSLog(@"小罪ADD: [tersafe 0x218D58 hook] ter线程范围检测触发 128出现，已替换");
						}
					}

					if (shujusize == 576) 
					{
						if (!cached_flag576) 
						{
							// 首次出现  576字节，缓存
				            memcpy((void *)cached_struct576, (void *)thread_state2.__x[0], 576);
				            cached_flag576 = true;
							NSLog(@"小罪ADD: [tersafe 0x218D58 hook] ter线程范围检测触发 576 首次出现，已记录");
						}
						else
						{
							memcpy((void *)thread_state2.__x[0], (void *)cached_struct576, 576);
							NSLog(@"小罪ADD: [tersafe 0x218D58 hook] ter线程范围检测触发 576 出现，已替换");
						}
					}

					if (shujusize == 160) 
					{
						if (!cached_flag160) 
						{
							// 首次出现 160 字节，缓存
				            memcpy((void *)cached_struct160, (void *)thread_state2.__x[0], 160);
				            cached_flag160 = true;
							NSLog(@"小罪ADD: [tersafe 0x218D58 hook] ter线程范围检测触发 160 首次出现，已记录");
						}
						else
						{
							memcpy((void *)thread_state2.__x[0], (void *)cached_struct160, 160);
							NSLog(@"小罪ADD: [tersafe 0x218D58 hook] ter线程范围检测触发 160 出现，已替换");
						}
					}

					if (shujusize == 400) 
					{
						if (!cached_flag400) 
						{
							// 首次出现 400 字节，缓存
				            memcpy((void *)cached_struct400, (void *)thread_state2.__x[0], 400);
				            cached_flag160 = true;
							NSLog(@"小罪ADD: [tersafe 0x218D58 hook] ter线程范围检测触发 400 首次出现，已记录");
						}
						else
						{
							memcpy((void *)thread_state2.__x[0], (void *)cached_struct400, 400);
							NSLog(@"小罪ADD: [tersafe 0x218D58 hook] ter线程范围检测触发 400 出现，已替换");
						}
					}

					if (shujusize == 1000) 
					{
						if (!cached_flag1000) 
						{
							// 首次出现 1000 字节，缓存
				            memcpy((void *)cached_struct1000, (void *)thread_state2.__x[0], 1000);
				            cached_flag1000 = true;
							NSLog(@"小罪ADD: [tersafe 0x218D58 hook] 主线程范围检测触发 1000 首次出现，已记录");
						}
						else
						{
							memcpy((void *)thread_state2.__x[0], (void *)cached_struct1000, 1000);
							NSLog(@"小罪ADD: [tersafe 0x218D58 hook] ter线程范围检测触发 1000 出现，已替换");
						}
					}

					
					//forcewritenew(thread_state2.__x[0] + 0x10, 1);
					//forcewritenew(thread_state2.__x[0] + 0x1C, 0 );
					//forcewritenew(thread_state2.__x[0] + 0x14, 0 );
					//forcewritenew(thread_state2.__x[0] + 0x18, 0);
					

					//memset((void*)thread_state2.__x[0], thread_state2.__x[0], shujusize);
					
					//thread_state2.__x[0] = 1;

					//bp->target = (uint64_t)(tersafeadd + 0x218D5C);
					

					//old
					thread_state2.__lr = (uint64_t)(tersafeadd + 0x218D5C);
					bp->target = (uint64_t)(tersafeadd + 0x210330);

			

					
				}
				else
				{
					NSLog(@"小罪ADD: [tersafe 0x218D58 hook] ter线程范围检测触发放行(非576或128)（sub_210330 RingBuf_Tick),a2 = %d,v2 = %d,biaoshi = %d,shujusize = %d",a2,v2,biaoshi,shujusize);

					
					
					thread_state2.__lr = (uint64_t)(tersafeadd + 0x218D5C);
					bp->target = (uint64_t)(tersafeadd + 0x210330);
					
					//memset((void*)thread_state2.__x[0], thread_state2.__x[0], shujusize);
					//thread_state2.__x[0] = 1;
					//bp->target = (uint64_t)(tersafeadd + 0x218D5C);
					
				}
				*/
				
				
				//NSLog(@"小罪ADD: [tersafe 0x24B47C hook] tersafe线程触发VM_DebugDetect_Dispatch 越狱检测");

				
				//NSLog(@"小罪ADD: [tersafe sub_241968 hook] tersafe模块 BufWriter_WriteField 触发");
				//NSLog(@"小罪ADD: [tersafe sub_1864C hook] tersafe模块环境检测触发");
				//sub_1E1E28 自瞄hook
				//NSLog(@"小罪ADD: [tersafe sub_1E1E28 hook] 自瞄hook检测触发");
				
				

				

			}

			
			if(terbptype == 3) 
			{	
				//0x20FCF4 ReportQueue_Enqueue write
				//NSLog(@"小罪ADD: [tersafe 0x20FCF4 hook] ter线程 ReportQueue_Enqueue write called");
			
				
				//异常上报 ReportQueue_Enqueue sub_210EAC
				uint64_t myptr = thread_state2.__x[1];
				int opcode = Read_Int(myptr);
				//const char* result = "";
				NSString *result = @"0";

				if(opcode < 0x100) result = @"小于0x100未的知异常";
				if(opcode >= 0x100 && opcode < 0x200) result = @"VM执行引擎异常、调试检测";
				if(opcode >= 0x200 && opcode < 0x300) result = @"Inline Hook / 代码完整性 / Session管理";
				if(opcode >= 0x300 && opcode < 0x400) result = @"VM opcode参数非法";
				if(opcode >= 0x400 && opcode < 0x500) result = @"VM opcode未知分支";
				if(opcode >= 0x500 && opcode < 0x600) result = @"定时器/调度系统异常";
				if(opcode >= 0x600 && opcode < 0x700) result = @"dladdr/内存映射异常";
				if(opcode >= 0x700 && opcode < 0x800) result = @"文件系统异常";
				if(opcode >= 0x800) result = @"超过0x800的未知异常";

				NSLog(@"小罪ADD: [tersafe sub_210EAC hook] ReportQueue_Enqueue tersafe线程 通道异常上报触发,opcode:%d,异常状态：%@",opcode,result);
				
				
				//NSLog(@"小罪ADD: [tersafe 0x2132C8 hook] ter线程 VM_DispatchPendingCallbacks called");
				
				
				/*
				uint64_t path_ptr = thread_state2.__x[2];
			    char path[1024] = {0};
			    mach_vm_size_t bytes_read = 0;
			    kern_return_t kr = mach_vm_read_overwrite(mach_task_self(), path_ptr, sizeof(path)-1,
			                                              (mach_vm_address_t)path, &bytes_read);
			    if (kr == KERN_SUCCESS && bytes_read > 0) 
				{
			        path[bytes_read] = '\0';
			        NSLog(@"小罪ADD: [tersafe sub_93E04 hook] ter线程 检测类型: %s", path);

					
			    } else 
				{
			        NSLog(@"小罪ADD: [tersafe sub_93E04 hook] ter线程 Failed to read 检测类型 at 0x%llx", path_ptr);
			    }
				*/
				
			
				//NSLog(@"小罪ADD: [tersafe sub_23B6A4(Timer_Fire) hook] ter线程调用");

				/*
				//下发检测hook sub_824AC
				uint64_t path_ptr = thread_state2.__x[1];
			    char path[1024] = {0};
			    mach_vm_size_t bytes_read = 0;
			    kern_return_t kr = mach_vm_read_overwrite(mach_task_self(), path_ptr, sizeof(path)-1,
			                                              (mach_vm_address_t)path, &bytes_read);
			    if (kr == KERN_SUCCESS && bytes_read > 0) 
				{
			        path[bytes_read] = '\0';
			        //NSLog(@"小罪ADD: [tersafe 下发检测：sub_824AC hook] ter线程 检测类型: %s", path);
				}
				*/

				
			}

			

			if(terbptype == 4) 
			{	
				NSLog(@"小罪ADD: [tersafe 0x93C10 hook] ter线程调用");
				

				//0x1E1E28
				//NSLog(@"小罪ADD: [tersafe 0x1E1E28 hook] tersafe线程 自瞄hook触发");


				/* 上报警告检测hook sub_824AC
				uint64_t path_ptr = thread_state2.__x[1];
			    char path[1024] = {0};
			    mach_vm_size_t bytes_read = 0;
			    kern_return_t kr = mach_vm_read_overwrite(mach_task_self(), path_ptr, sizeof(path)-1,
			                                              (mach_vm_address_t)path, &bytes_read);
			    if (kr == KERN_SUCCESS && bytes_read > 0) 
				{
			        path[bytes_read] = '\0';
			        NSLog(@"小罪ADD: [tersafe 警告上报sub_824AC hook] 检测类型: %s", path);

					
			    } else 
				{
			        NSLog(@"小罪ADD: [tersafe 警告上报sub_824AC hook] Failed to read 检测类型 at 0x%llx", path_ptr);
			    }
				*/
				
				
				
			}
 
			if(terbptype == 5)  
			{	
				//0xAA880 检测控制开关

				bool iscontainstr = false;
				//全局检测开关hook sub_AA880
				uint64_t path_ptr = thread_state2.__x[1];
			    char path[1024] = {0};
			    mach_vm_size_t bytes_read = 0;
			    kern_return_t kr = mach_vm_read_overwrite(mach_task_self(), path_ptr, sizeof(path)-1,
			                                              (mach_vm_address_t)path, &bytes_read);
			    if (kr == KERN_SUCCESS && bytes_read > 0) 
				{
			        path[bytes_read] = '\0';
			        //NSLog(@"小罪ADD: [tersafe 全局检测开关 sub_AA880 hook] 检测类型: %s", path);

					const char* result = "";

					result = strstr(path, "force");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "enc");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "hb");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "jb");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "jail");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "cs3");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "port_80");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, ".img");
					if (result != NULL) iscontainstr = true;

					/*
					result = strstr(path, "scan");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "report");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "screenshot");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "process");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "dylib");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "900");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "module");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "hook");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "check");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "cert");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "IDFV");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "chk");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "jb");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "jail");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "tfp");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "hook");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "device");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "TDM");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "tdm");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "force");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "enc");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "hb");
					if (result != NULL) iscontainstr = true;

					//result = strstr(path, "Logout");
					//if (result != NULL) iscontainstr = true;


					
					//result = strstr(path, "mrpcs"); //会三方
					//if (result != NULL) iscontainstr = true;
					
					
					result = strstr(path, "anti");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "cs3");
					if (result != NULL) iscontainstr = true;

					//上面全部关闭也会三方
					
					
					
					result = strstr(path, "ts");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "tcj");
					if (result != NULL) iscontainstr = true;

					
					result = strstr(path, "gcloud");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "sc");
					if (result != NULL) iscontainstr = true;

					
					result = strstr(path, "dl");
					if (result != NULL) iscontainstr = true;
					

					
					//result = strstr(path, "mrmoni");  //会三方
					//if (result != NULL) iscontainstr = true;
					

					
					result = strstr(path, "sav");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "ac");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "ios");
					if (result != NULL) iscontainstr = true;
					
					result = strstr(path, "ob");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, ".img");
					if (result != NULL) iscontainstr = true;

					
					result = strstr(path, "filt");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "ne");
					if (result != NULL) iscontainstr = true;
					

					
					result = strstr(path, "mt");
					if (result != NULL) iscontainstr = true;

					

					
					result = strstr(path, "game");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "Game");
					if (result != NULL) iscontainstr = true;
					

					
					result = strstr(path, "ip");
					if (result != NULL) iscontainstr = true;

					result = strstr(path, "ds");
					if (result != NULL) iscontainstr = true;
					
					result = strstr(path, "port");
					if (result != NULL) iscontainstr = true;
					*/

					

					if(iscontainstr == true)
					{
						NSLog(@"小罪ADD: [tersafe 全局检测开关 sub_AA880 hook] tersafe线程 准备干掉字符串并返回0: %s", path);
						bp->target = (uint64_t)(hooked_ret0);
						//thread_state2.__sp -= 0x40;
						//bp->target = (uint64_t)(thread_state2.__pc + 4);
					}
					else
					{
						//NSLog(@"小罪ADD: [tersafe 全局检测开关 sub_AA880 hook] tersafe线程 暂时不干掉的检测类型: %s", path);
						thread_state2.__sp -= 0x40;
						bp->target = (uint64_t)(thread_state2.__pc + 4);
					}

					
			    } else 
				{
			        NSLog(@"小罪ADD: [tersafe 全局检测开关 sub_AA880 hook] tersafe线程 Failed to read 检测类型 at 0x%llx", path_ptr);
					// 模拟 SUB SP, SP, #0x40
					thread_state2.__sp -= 0x40;
					bp->target = (uint64_t)(thread_state2.__pc + 4);
			    }
			
				/*
				//0x2A2B0 _tp2_setuserinfo
				NSLog(@"小罪ADD: [tersafe 0x2A2B0 hook] _tp2_setuserinfo ter线程 called !");

				thread_state2.__x[0] = 3;

				//先还原
			    uint64_t sp = thread_state2.__sp;
				
			    //uint64_t new_x29 = sp + 0x50;
			    //thread_state2.__x[29] = new_x29;   // X29 即帧指针
				
				uint64_t new_x29 = sp + 0x50;
			    thread_state2.__fp = new_x29;   // 使用 __fp 而不是 __x[29]

				uint64_t open_id_ptr = thread_state2.__x[2];
			    char open_idpath1[1024] = {0};
			    mach_vm_size_t bytes_read1 = 0;
			    kern_return_t kr = mach_vm_read_overwrite(mach_task_self(), open_id_ptr, sizeof(open_idpath1)-1,
			                                              (mach_vm_address_t)open_idpath1, &bytes_read1);
				uint64_t role_id_ptr = thread_state2.__x[3];
			    char role_idpath2[1024] = {0};
			    mach_vm_size_t bytes_read2 = 0;
			    kr = mach_vm_read_overwrite(mach_task_self(), role_id_ptr, sizeof(role_idpath2)-1,
			                                              (mach_vm_address_t)role_idpath2, &bytes_read2);
	
			    if (kr == KERN_SUCCESS && bytes_read1 > 0 && bytes_read2 > 0) 
				{
			        open_idpath1[bytes_read1] = '\0';
					role_idpath2[bytes_read2] = '\0';
			        NSLog(@"小罪ADD: [tersafe ter线程 0x2A2B0 hook] ter线程触发 _tp2_setuserinfo open_id: %s ,role_id: %s",open_idpath1 , role_idpath2);

					//open_idpath1: 7916182520048297861

					if(open_idpath1)
					{
						const char *new_open_id   = "7916182520048297861";

						size_t write_len = strlen(new_open_id) + 1; // 19 + 1 = 20
				        kr = mach_vm_write(mach_task_self(), open_id_ptr, (mach_vm_address_t)new_open_id, write_len);
				        if (kr == KERN_SUCCESS) 
						{
							kr = mach_vm_write(mach_task_self(), role_id_ptr, (mach_vm_address_t)new_open_id, write_len);
				             NSLog(@"小罪ADD: [tersafe ter线程 0x2A2B0 hook] ter线程触发 成功将 open_id 替换为 %s", new_open_id);
				        } else {
				            NSLog(@"小罪ADD: [tersafe ter线程 0x2A2B0 hook]  ter线程触发 mach_vm_write 失败: %s", mach_error_string(kr));
				        }

					}

			    } 
				else 
				{
			        NSLog(@"小罪ADD: [tersafe ter线程 0x2A2B0 hook] ter线程 触发 _tp2_setuserinfo Failed to read open_id at 0x%llx,role_id at 0x%llx,", open_id_ptr,role_id_ptr);
			    }
				*/
			
				/*
				//0x33DA4 tp2_setgamestatus
				uint64_t a1 = thread_state2.__x[0];
				NSLog(@"小罪ADD: [tersafe 0x33DA4 hook] ter线程触发 tp2_setgamestatus a2:%d",a1); 

				if(a1 == 1)// || a2 == 3
				{
					thread_state2.__x[1] = 2;
					//bp->target = (uint64_t)(hooked_ret0);
					NSLog(@"小罪ADD: [tersafe 0x33DA4 hook] ter线程触发 TssSDKOnResume 触发：a1:%d改为:%d",a1,thread_state2.__x[1]);
					thread_state2.__sp = thread_state2.__sp - 0x20;
					bp->target = (uint64_t)(tersafeadd + 0x33DA8);
				}
				else
				{
					NSLog(@"小罪ADD: [tersafe 0x33DA4 hook] ter线程触发 TssSDKOnPause 触发，放行");
					thread_state2.__sp = thread_state2.__sp - 0x20;
					bp->target = (uint64_t)(tersafeadd + 0x33DA8);
				}
				*/

			
				/*
				//0x3F744 TssSDKDispatchMonitorEvent
				uint64_t a2 = thread_state2.__x[1];
				NSLog(@"小罪ADD: [tersafe 0x3F744 hook] ter线程触发TssSDKDispatchMonitorEvent a2:%d,直接返回0",a2); 
				*/

				/*
				if(a2 == 2)// || a2 == 3
				{
					thread_state2.__x[1] = 3;
					//bp->target = (uint64_t)(hooked_ret0);
					NSLog(@"小罪ADD: [tersafe 0x3F744 hook] ter线程触发TssSDKDispatchMonitorEvent TssSDKOnPause触发：a2:%d改为:%d",a2,thread_state2.__x[1]);
					thread_state2.__sp = thread_state2.__sp - 0x30;
					bp->target = (uint64_t)(tersafeadd + 0x3F748);
				}
				else
				{
					thread_state2.__sp = thread_state2.__sp - 0x30;
					bp->target = (uint64_t)(tersafeadd + 0x3F748);
				}
				*/
				
			
			
				//0x154108 commit_patch_memory
				//NSLog(@"小罪ADD: [tersafe 0x154108 hook] tersafe线程触发commit_patch_memory"); 
			
				
				//0x193F90
				//NSLog(@"小罪ADD: [tersafe 0x193F90 hook] tersafe线程 游戏自带hook触发");
				
				//sub_1371C0 环境检测
				//NSLog(@"小罪ADD: [sub_1000475C8 hook] 主线程环境检测触发");
				//NSLog(@"小罪ADD: [tersafe 0x133124 hook] tersafe线程环境检测");
				
				

			}

			
			
		}


		
        // 修改 PC 为目标地址（断点持续有效）
        //arm_thread_state64_set_pc(thread_state, bp->target);
		thread_state2.__pc = (uint64_t)bp->target;
        thread_set_state(thread_port, ARM_THREAD_STATE64,(thread_state_t)&thread_state2, ARM_THREAD_STATE64_COUNT);

    	send_reply:
        // 回复异常已处理
		{
	        struct {
	            mach_msg_header_t head;
	            NDR_record_t ndr;
	            kern_return_t ret;
	        } reply;
	        reply.head.msgh_bits = MACH_MSGH_BITS(MACH_MSGH_BITS_REMOTE(msg.head.msgh_bits), 0);
	        reply.head.msgh_size = sizeof(reply);
	        reply.head.msgh_remote_port = msg.head.msgh_remote_port;
	        reply.head.msgh_local_port = MACH_PORT_NULL;
	        reply.head.msgh_id = msg.head.msgh_id + 100;
	        reply.ndr = NDR_record;
	        reply.ret = KERN_SUCCESS;
	
	        mach_msg(&reply.head, MACH_SEND_MSG, reply.head.msgh_size, 0,
	                 MACH_PORT_NULL, MACH_MSG_TIMEOUT_NONE, MACH_PORT_NULL);
	
	        mach_msg_destroy(&msg.head);
		}
    }

    return NULL;
}


void initbreakpoint()
{
	NSLog(@"小罪ADD: initbreakpoint: loaded, setting up hardware breakpoint...");

	NSLog(@"小罪ADD: initbreakpoint: jump_hook dylib loaded");


	/*
    // 注册 SIGTRAP 信号处理器
	stack_t sig_stack;
    sig_stack.ss_sp = malloc(SIGSTKSZ);
    sig_stack.ss_size = SIGSTKSZ;
    sig_stack.ss_flags = 0;
    sigaltstack(&sig_stack, NULL);
	
    struct sigaction sa;
    //sa.sa_flags = SA_SIGINFO | SA_RESTART;
	//sa.sa_flags = SA_SIGINFO | SA_RESTART | SA_NODEFER;
	sa.sa_flags = SA_SIGINFO | SA_RESTART | SA_NODEFER | SA_ONSTACK;
    sa.sa_sigaction = sigtrap_handler;
    sigemptyset(&sa.sa_mask);
    if (sigaction(SIGTRAP, &sa, NULL) == -1)
	{
        NSLog(@"小罪ADD: initbreakpoint: Failed to install SIGTRAP handler");
        return;
    }
	else
	{
		NSLog(@"小罪ADD: initbreakpoint: install SIGTRAP handler success !");
	}
	*/

	/*
	//开始对游戏内存进行hook
	//mach_vm_address_t wuhouadd = Imageaddress + 0x2F72298;
	//g_source_addr = Imageaddress + 0x2F72298;
	//g_target_addr = g_source_addr + 4;

	// old设置单个硬件断点
    kern_return_t kr = set_hw_breakpoint(g_source_addr);
    while (kr != KERN_SUCCESS) 
	{
        NSLog(@"小罪ADD: initbreakpoint: Failed to set hardware breakpoint at 0x%llx", g_source_addr);
		sleep(5);
		kr = set_hw_breakpoint(g_source_addr);
        //return;
    }
	
    NSLog(@"小罪ADD: initbreakpoint: Persistent hardware breakpoint set at 0x%llx, will jump to 0x%llx on each hit",
          g_source_addr, g_target_addr);
	*/

	mach_vm_address_t wuhouadd   = Imageaddress + 0x3355BF0 ;
	mach_vm_address_t fanweiadd1 = Imageaddress + 0x1828738 ;
    mach_vm_address_t fanweiadd2 = Imageaddress + 0x1828760 ;
    mach_vm_address_t fanweiadd3 = Imageaddress + 0x1827FD8 ;
    mach_vm_address_t fanweiadd4 = Imageaddress + 0x1828000 ;

	mach_vm_address_t tersafetsadd1 = tersafeadd + 0x582A4;
	mach_vm_address_t tersafetsadd1ret = (mach_vm_address_t)hooked_sub_585D0;

	mach_vm_address_t tersafetsadd2 = tersafeadd + 0x582A4;
	mach_vm_address_t tersafetsadd2ret = (mach_vm_address_t)hooked_sub_585D0;

	mach_vm_address_t tersafetsadd3 = tersafeadd + 0x241578;//范围检测1
	mach_vm_address_t tersafetsadd3ret = (mach_vm_address_t)hooked_sub241578;//tersafeadd + 0x241814;

	mach_vm_address_t tersafetsadd4 = tersafeadd + 0x23B6A4;;//范围检测2
	mach_vm_address_t tersafetsadd4ret = (mach_vm_address_t)hooked_ret8;//tersafeadd + 0x241914;

	//mach_vm_address_t tersafetsadd4 = tersafeadd + 0x241578;//范围检测1
	//mach_vm_address_t tersafetsadd4ret = (mach_vm_address_t)hooked_sub241578;//tersafeadd + 0x241814;

	mach_vm_address_t tersafetsadd5 = tersafeadd + 0x23A448;//范围检测3 禁止启动县城
	mach_vm_address_t tersafetsadd5ret = (mach_vm_address_t)hooked_ret0;//tersafeadd + 0x241914;

	mach_vm_address_t tersafetsadd6 = tersafeadd + 0x23DA74;//范围检测3 禁止启动县城
	mach_vm_address_t tersafetsadd6ret = (mach_vm_address_t)hooked_ret0;//tersafeadd + 0x23DA74;

	//新增过检测

	mach_vm_address_t tersafetsadd7 = tersafeadd + 0x134DC8;//
	mach_vm_address_t tersafetsadd7ret = (mach_vm_address_t)hooked_ret1;//tersafeadd + 0x23DA74;

	mach_vm_address_t tersafetsadd8 = tersafeadd + 0x17ECDC;//
	mach_vm_address_t tersafetsadd8ret = (mach_vm_address_t)hooked_ret1;//tersafeadd + 0x23DA74;

	mach_vm_address_t tersafetsadd9 = tersafeadd + 0x1BB584;//
	mach_vm_address_t tersafetsadd9ret = (mach_vm_address_t)hooked_ret1;//tersafeadd + 0x23DA74;

	mach_vm_address_t tersafetsadd10 = tersafeadd + 0x133124;//
	mach_vm_address_t tersafetsadd10ret = (mach_vm_address_t)hooked_ret1;//tersafeadd + 0x23DA74;

	//ai过检测

	mach_vm_address_t tersafetsadd11 = tersafeadd + 0x6CF8;//
	mach_vm_address_t tersafetsadd11ret = (mach_vm_address_t)hooked_ret0;

	mach_vm_address_t tersafetsadd12 = tersafeadd + 0x3FCE8;//
	mach_vm_address_t tersafetsadd12ret = (mach_vm_address_t)hooked_ret0;

	mach_vm_address_t tersafetsadd13= tersafeadd + 0x41F10;//
	mach_vm_address_t tersafetsadd13ret = (mach_vm_address_t)hooked_ret0;

	mach_vm_address_t tersafetsadd14 = tersafeadd + 0xF9584;//
	mach_vm_address_t tersafetsadd14ret = (mach_vm_address_t)hooked_ret0;

	mach_vm_address_t tersafetsadd15 = tersafeadd + 0x100B3C;//
	mach_vm_address_t tersafetsadd15ret = (mach_vm_address_t)hooked_ret0;

	//ai过检测2
	mach_vm_address_t tersafetsadd16 = tersafeadd + 0x413AC;//
	mach_vm_address_t tersafetsadd16ret = (mach_vm_address_t)hooked_ret0;

	//ai过检测3
	mach_vm_address_t tersafetsadd17 = tersafeadd + 0x108DC4;//
	mach_vm_address_t tersafetsadd17ret = (mach_vm_address_t)hooked_ret0;

	mach_vm_address_t tersafetsadd18 = tersafeadd + 0xAA880;//
	mach_vm_address_t tersafetsadd18ret = tersafeadd + 0xAA884;//

	mach_vm_address_t tersafetsadd19 = tersafeadd + 0x824AC;//
	mach_vm_address_t tersafetsadd19ret = (mach_vm_address_t)hooked_ret0;

	mach_vm_address_t tersafetsadd20 = tersafeadd + 0x93D34;//
	mach_vm_address_t tersafetsadd20ret = (mach_vm_address_t)hooked_ret0;


	//3.28ai过检测
	mach_vm_address_t tersafetsadd21 = tersafeadd + 0x241578;//
	//mach_vm_address_t tersafetsadd21ret = (mach_vm_address_t)hooked_sub241578;
	mach_vm_address_t tersafetsadd21ret = (mach_vm_address_t)hooked_ret1;

	mach_vm_address_t tersafetsadd22 = tersafeadd + 0x210EAC;//
	mach_vm_address_t tersafetsadd22ret = (mach_vm_address_t)hooked_ret0;

	mach_vm_address_t tersafetsadd23 = tersafeadd + 0x258948;//
	mach_vm_address_t tersafetsadd23ret = tersafeadd + 0x258950;

	mach_vm_address_t tersafetsadd24 = tersafeadd + 0x218D58;//单纯范围的检测
	mach_vm_address_t tersafetsadd24ret = tersafeadd + 0x218D5C;

	mach_vm_address_t tersafetsadd25 = tersafeadd + 0x1E1E28;//自瞄hook检测
	mach_vm_address_t tersafetsadd25ret = (mach_vm_address_t)hooked_ret1;


	//4.1 新的环境检测
	mach_vm_address_t tersafetsadd26 = tersafeadd + 0x1864C;//环境
	mach_vm_address_t tersafetsadd26ret = (mach_vm_address_t)hooked_ret0;

	mach_vm_address_t tersafetsadd27 = tersafeadd + 0x133124;//环境
	mach_vm_address_t tersafetsadd27ret = (mach_vm_address_t)hooked_ret0;

	//4.2环境
	mach_vm_address_t zhuxianchenghjadd1 = Imageaddress + 0x1000475C8;
	mach_vm_address_t zhuxianchenghjadd1ret = (mach_vm_address_t)hooked_ret0;

	//4.3上报
	mach_vm_address_t tersafetsadd28 = tersafeadd + 0x241968;
	mach_vm_address_t tersafetsadd28ret = (mach_vm_address_t)hooked_ret1;

	mach_vm_address_t tersafetsadd29 = tersafeadd + 0x24B47C;//
	mach_vm_address_t tersafetsadd29ret = (mach_vm_address_t)hooked_ret8;

	mach_vm_address_t tersafetsadd30 = tersafeadd + 0x2412D0;//BufWriter_Init
	mach_vm_address_t tersafetsadd30ret = tersafeadd + 0x2412D4;

	//4.6闪退
	mach_vm_address_t tersafetsadd31 = tersafeadd + 0x254818;//VM_DebugDetect_Instance2
	mach_vm_address_t tersafetsadd31ret = (mach_vm_address_t)hooked_ret1;

	//
	mach_vm_address_t tersafetsadd32 = tersafeadd + 0x193F90;//游戏内置hook
	mach_vm_address_t tersafetsadd32ret = tersafeadd + 0x194028;

	mach_vm_address_t tersafetsadd33 = tersafeadd + 0x93E04;//
	mach_vm_address_t tersafetsadd33ret = (mach_vm_address_t)hooked_ret0;

	mach_vm_address_t tersafetsadd34 = tersafeadd + 0x93C10;//
	mach_vm_address_t tersafetsadd34ret = tersafeadd + 0x93C30;

	mach_vm_address_t calladd1 = Imageaddress + 0x629AC1C;
	mach_vm_address_t calladd1ret = (mach_vm_address_t)hooked_ret0;

	mach_vm_address_t calladd2 = Imageaddress + 0x7A120BC;
	mach_vm_address_t calladd2ret = (mach_vm_address_t)hooked_ret0;

	mach_vm_address_t calladd3 = Imageaddress + 0x124DA40;//0x8E312E8
	mach_vm_address_t calladd3ret = Imageaddress + 0x124DA44;

	mach_vm_address_t tersafetsadd35 = tersafeadd + 0x97C68;//EventReport_Dispatch
	mach_vm_address_t tersafetsadd35ret = (mach_vm_address_t)hooked_ret0;

	mach_vm_address_t tersafetsadd36 = tersafeadd + 0x939A4;//ScanEngine_GetInstance
	mach_vm_address_t tersafetsadd36ret = tersafeadd + 0x939B4;

	mach_vm_address_t tersafetsadd37 = tersafeadd + 0x20F42C;//NetObj_GetInstance
	mach_vm_address_t tersafetsadd37ret = (mach_vm_address_t)hooked_ret0;

	mach_vm_address_t calladd4 = Imageaddress + 0x18791C8;//
	mach_vm_address_t calladd4ret = (mach_vm_address_t)hooked_ret0;

	mach_vm_address_t tersafetsadd38 = tersafeadd + 0x2132C8;//VM_DispatchPendingCallbacks
	mach_vm_address_t tersafetsadd38ret = (mach_vm_address_t)hooked_ret0;

	mach_vm_address_t tersafetsadd39 = tersafeadd + 0x2B2AC;//tss_get_report_data2
	mach_vm_address_t tersafetsadd39ret = (mach_vm_address_t)hooked_ret2B8E32;

	mach_vm_address_t tersafetsadd40 = tersafeadd + 0x21033C;//全量范围检测
	mach_vm_address_t tersafetsadd40ret = tersafeadd + 0x210340;

	mach_vm_address_t tersafetsadd41 = tersafeadd + 0x2A2B0;//_tp2_setuserinfo
	mach_vm_address_t tersafetsadd41ret = tersafeadd + 0x2A2B4;

	mach_vm_address_t tersafetsadd42 = tersafeadd + 0x20FCF4;//sub_20FCF4 跟 ReportQueue_Enqueue有关的wirte
	mach_vm_address_t tersafetsadd42ret = (mach_vm_address_t)hooked_reta1;

	mach_vm_address_t tersafetsadd43 = tersafeadd + 0x2103B8;//sub_2103B8 上面的闪退处理
	mach_vm_address_t tersafetsadd43ret = (mach_vm_address_t)hooked_ret1;

	mach_vm_address_t tersafetsadd44 = tersafeadd + 0x20FD6C;//sub_20FD6C 查询容器容量
	mach_vm_address_t tersafetsadd44ret = (mach_vm_address_t)hooked_ret0;

	mach_vm_address_t tersafetsadd45 = tersafeadd + 0x154108;//sub_154108 commit_patch_memory
	mach_vm_address_t tersafetsadd45ret = (mach_vm_address_t)hooked_ret1;

	mach_vm_address_t tersafetsadd46 = tersafeadd + 0x3F744;//sub_3F744 TssSDKDispatchMonitorEvent
	mach_vm_address_t tersafetsadd46ret = (mach_vm_address_t)hooked_ret0;
	//mach_vm_address_t tersafetsadd46ret = tersafeadd + 0x3F748;

	mach_vm_address_t tersafetsadd47 = tersafeadd + 0x33DA4;//sub_33DA4 tp2_setgamestatus
	mach_vm_address_t tersafetsadd47ret = tersafeadd + 0x33DA8;

	mach_vm_address_t tersafetsadd48 = tersafeadd + 0xF6260;//sub_F6260 down 
	mach_vm_address_t tersafetsadd48ret = (mach_vm_address_t)hooked_ret1;

	mach_vm_address_t tersafetsadd49 = tersafeadd + 0xA4DE4;//sub_A4DE4 nj 
	mach_vm_address_t tersafetsadd49ret = (mach_vm_address_t)hooked_ret0;

	mach_vm_address_t DataFromTGPAadd1 = Imageaddress + 0x81B241C;
	mach_vm_address_t DataFromTGPAadd1ret = (mach_vm_address_t)hooked_ret0;

	mach_vm_address_t DataFromTGPAadd2 = Imageaddress + 0xC4086C4;
	mach_vm_address_t DataFromTGPAadd2ret = (mach_vm_address_t)hooked_ret0;

	//禁止hook
	mach_vm_address_t tersafetsadd50 = tersafeadd + 0x170278;//sub_170278 全局游戏hook
	mach_vm_address_t tersafetsadd50ret = tersafeadd + 0x170388;

	mach_vm_address_t tersafetsadd51 = tersafeadd + 0x1AEB30;//sub_1AEB30 自瞄hook
	mach_vm_address_t tersafetsadd51ret = (mach_vm_address_t)hooked_ret1;

	//范围检测
	mach_vm_address_t tersafetsadd52 = tersafeadd + 0x210330;//sub_210330 范围上报检测
	mach_vm_address_t tersafetsadd52ret = (mach_vm_address_t)hooked_ret1;

	mach_vm_address_t shantuiadd2 = Imageaddress + 0x821F948;
	mach_vm_address_t shantuiadd2ret = (mach_vm_address_t)hooked_ret1;

	mach_vm_address_t shantuiadd3 = Imageaddress + 0x801E5F4;
	//mach_vm_address_t shantuiadd3ret = (mach_vm_address_t)hooked_ret0;
	mach_vm_address_t shantuiadd3ret = Imageaddress + 0x801E5F8;

	g_source_addr = wuhouadd;
	g_target_addr = wuhouadd + 4;
	

	
	g_breakpoints[0] = (Breakpoint){
        .source = wuhouadd,          // 源地址
        .target = wuhouadd + 4,          // 目标地址
        .s0_val = -0.02f,             // 要写入 s0 的值
        .s1_val = -0.02f,             // 要写入 s1 的值
        .used = 1,
        .hw_index = -1
    };


	/*
	//0x154108 commit_patch_memory
	g_breakpoints[1] = (Breakpoint){
        .source = tersafetsadd45,
        .target = tersafetsadd45ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	//0x3F744 TssSDKDispatchMonitorEvent
	g_breakpoints[1] = (Breakpoint){
        .source = tersafetsadd46,
        .target = tersafetsadd46ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	//0x2A2B0 _tp2_setuserinfo
	g_breakpoints[1] = (Breakpoint){
        .source = tersafetsadd41,
        .target = tersafetsadd41ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	//0xAA880 检测控制开关
	g_breakpoints[1] = (Breakpoint){
        .source = tersafetsadd18,
        .target = tersafetsadd18ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	//0x6CF8 环境
	g_breakpoints[1] = (Breakpoint){
        .source = tersafetsadd11,
        .target = tersafetsadd11ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	//0x20FD6C 查询容器容量
	g_breakpoints[1] = (Breakpoint){
        .source = tersafetsadd44,
        .target = tersafetsadd44ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	//0x801E5F4 shantuiadd3
	g_breakpoints[1] = (Breakpoint){
        .source = shantuiadd3,
        .target = shantuiadd3ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };

	/*
	//0xF6260 down
	g_breakpoints[1] = (Breakpoint){
        .source = tersafetsadd48,
        .target = tersafetsadd48ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/
	

	/*
	//0x170278 全局游戏hook
	g_breakpoints[1] = (Breakpoint){
        .source = tersafetsadd50,
        .target = tersafetsadd50ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/
	

	/*
	//sub_1081B241C DataFromTGPAcalladd
	g_breakpoints[1] = (Breakpoint){
        .source = DataFromTGPAadd1,
        .target = DataFromTGPAadd1ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	//0x33DA4 tp2_setgamestatus
	g_breakpoints[1] = (Breakpoint){
        .source = tersafetsadd47,
        .target = tersafetsadd47ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	//0x93978 ScanEngine_GetInstance
	g_breakpoints[2] = (Breakpoint){
        .source = tersafetsadd36,
        .target = tersafetsadd36ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	g_breakpoints[2] = (Breakpoint){
        .source = calladd3,
        .target = calladd3ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	
	//0x218D58 RingBuf_Tick
	g_breakpoints[2] = (Breakpoint){
        .source = tersafetsadd24,
        .target = tersafetsadd24ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	
	/*
	//0x210330 范围上报检测
	g_breakpoints[2] = (Breakpoint){
        .source = tersafetsadd52,
        .target = tersafetsadd52ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	//RingBuf_Ticknew
	g_breakpoints[2] = (Breakpoint){
        .source = tersafetsadd40,
        .target = tersafetsadd40ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	
	//0x210EAC ReportQueue_Enqueue  很重要，没有就直接三方了
	g_breakpoints[3] = (Breakpoint){
        .source = tersafetsadd22,
        .target = tersafetsadd22ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	

	/*
	//0x20FCF4 ReportQueue_Enqueue write
	g_breakpoints[3] = (Breakpoint){
        .source = tersafetsadd42,
        .target = tersafetsadd42ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	//sub_107A120BC
	g_breakpoints[4] = (Breakpoint){
        .source = calladd2,
        .target = calladd2ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/
	
	/*
	//NetObj_GetInstance
	g_breakpoints[4] = (Breakpoint){
        .source = tersafetsadd37,
        .target = tersafetsadd37ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	//0xA4DE4 nj
	g_breakpoints[4] = (Breakpoint){
        .source = tersafetsadd49,
        .target = tersafetsadd49ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	//0x1AEB30 自瞄hook
	g_breakpoints[4] = (Breakpoint){
        .source = tersafetsadd51,
        .target = tersafetsadd51ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	//0x821F948 shantuiadd2
	g_breakpoints[4] = (Breakpoint){
        .source = shantuiadd2,
        .target = shantuiadd2ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };

	

	/*
	//0x2B2AC tss_get_report_data2
	g_breakpoints[4] = (Breakpoint){
        .source = tersafetsadd39,
        .target = tersafetsadd39ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	
	g_breakpoints[5] = (Breakpoint){
        .source = fanweiadd3,
        .target = fanweiadd3 + 4,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	
	

	/*
	//0x582A4 下发
	g_breakpoints[1] = (Breakpoint){
        .source = tersafetsadd1,
        .target = tersafetsadd1ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/
	

	/*
	//0x24B47C VM_DebugDetect_Dispatch 越狱检测
	g_breakpoints[1] = (Breakpoint){
        .source = tersafetsadd29,
        .target = tersafetsadd29ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	//0x824AC 上报警告
	g_breakpoints[1] = (Breakpoint){
        .source = tersafetsadd19,
        .target = tersafetsadd19ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	

	/*
	g_breakpoints[4] = (Breakpoint){
        .source = tersafetsadd32,
        .target = tersafetsadd32ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	//BufWriter_WriteField
	g_breakpoints[4] = (Breakpoint){
        .source = tersafetsadd28,
        .target = tersafetsadd28ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/


	/*
	g_breakpoints[4] = (Breakpoint){
        .source = fanweiadd1,
        .target = fanweiadd1 + 4,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/


	/*
	g_breakpoints[5] = (Breakpoint){
        .source = tersafetsadd30,
        .target = tersafetsadd30ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	g_breakpoints[2] = (Breakpoint){
        .source = fanweiadd1,
        .target = fanweiadd1 + 4,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };

	g_breakpoints[3] = (Breakpoint){
        .source = fanweiadd2,
        .target = fanweiadd2 + 4,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };

	g_breakpoints[4] = (Breakpoint){
        .source = fanweiadd3,
        .target = fanweiadd3 + 4,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	g_breakpoints[5] = (Breakpoint){
        .source = fanweiadd4,
        .target = fanweiadd4 + 4,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/
	

    // 可以继续添加更多，但不要超过 MAX_HW_BREAKPOINTS (6)
    g_breakpoint_count = 6;

	/*
	//0x2103B8 新写法闪退
	ter_breakpoints[0] = (Breakpoint){
        .source = tersafetsadd43,
        .target = tersafetsadd43ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	//0x20FD6C 查询容器容量
	ter_breakpoints[0] = (Breakpoint){
        .source = tersafetsadd44,
        .target = tersafetsadd44ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	//0x801E5F4 shantuiadd3
	ter_breakpoints[0] = (Breakpoint){
        .source = shantuiadd3,
        .target = shantuiadd3ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	

	/*
	//0xF6260 down
	ter_breakpoints[0] = (Breakpoint){
        .source = tersafetsadd48,
        .target = tersafetsadd48ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/
	

	/*
	//0x170278 全局游戏hook
	ter_breakpoints[0] = (Breakpoint){
        .source = tersafetsadd50,
        .target = tersafetsadd50ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/


	/*
	//0xAA880 控制检测开关
	ter_breakpoints[0] = (Breakpoint){
        .source = tersafetsadd18,
        .target = tersafetsadd18ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	//0x582A4 下发
	ter_breakpoints[0] = (Breakpoint){
        .source = tersafetsadd1,
        .target = tersafetsadd1ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/


	/*
	//0x254818 VM_DebugDetect_Instance2
	ter_breakpoints[0] = (Breakpoint){
        .source = tersafetsadd31,
        .target = tersafetsadd31ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	//0x93978 ScanEngine_GetInstance
	ter_breakpoints[0] = (Breakpoint){
        .source = tersafetsadd36,
        .target = tersafetsadd36ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/
	
	//0x2132C8 VM_DispatchPendingCallbacks
	ter_breakpoints[1] = (Breakpoint){
        .source = tersafetsadd38,
        .target = tersafetsadd38ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };

	/*
	//0x218D58 RingBuf_Tick
	ter_breakpoints[2] = (Breakpoint){
        .source = tersafetsadd24,
        .target = tersafetsadd24ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	//0x6CF8 环境
	ter_breakpoints[2] = (Breakpoint){
        .source = tersafetsadd11,
        .target = tersafetsadd11ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	//0xA4DE4 nj
	ter_breakpoints[2] = (Breakpoint){
        .source = tersafetsadd49,
        .target = tersafetsadd49ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/
	

	/*
	//0x1AEB30 自瞄hook
	ter_breakpoints[2] = (Breakpoint){
        .source = tersafetsadd51,
        .target = tersafetsadd51ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	//0x20F42C NetObj_GetInstance
	ter_breakpoints[2] = (Breakpoint){
        .source = tersafetsadd37,
        .target = tersafetsadd37ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };

	/*
	//RingBuf_Ticknew
	ter_breakpoints[2] = (Breakpoint){
        .source = tersafetsadd40,
        .target = tersafetsadd40ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	
	//0x210EAC ReportQueue_Enqueue
	ter_breakpoints[3] = (Breakpoint){
        .source = tersafetsadd22,
        .target = tersafetsadd22ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	

	/*
	//0x20FCF4 ReportQueue_Enqueue write
	ter_breakpoints[3] = (Breakpoint){
        .source = tersafetsadd42,
        .target = tersafetsadd42ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/
	
	// 0x93C10 闪退
	ter_breakpoints[4] = (Breakpoint){
        .source = tersafetsadd34,
        .target = tersafetsadd34ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };



	/*
	//0x154108 commit_patch_memory
	ter_breakpoints[5] = (Breakpoint){
        .source = tersafetsadd45,
        .target = tersafetsadd45ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	//0x3F744 TssSDKDispatchMonitorEvent
	ter_breakpoints[5] = (Breakpoint){
        .source = tersafetsadd46,
        .target = tersafetsadd46ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	//0x2A2B0 _tp2_setuserinfo
	ter_breakpoints[5] = (Breakpoint){
        .source = tersafetsadd41,
        .target = tersafetsadd41ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	
	//0xAA880 检测控制开关
	ter_breakpoints[5] = (Breakpoint){
        .source = tersafetsadd18,
        .target = tersafetsadd18ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	


	/*
	//0x33DA4 tp2_setgamestatus
	ter_breakpoints[5] = (Breakpoint){
        .source = tersafetsadd47,
        .target = tersafetsadd47ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	

	/* 举报三天
	//0x24B47C VM_DebugDetect_Dispatch 越狱检测
	ter_breakpoints[2] = (Breakpoint){
        .source = tersafetsadd29,
        .target = tersafetsadd29ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	//0x23B6A4 Timer_Fire
	ter_breakpoints[3] = (Breakpoint){
        .source = tersafetsadd4,
        .target = tersafetsadd4ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	//0x241968 BufWriter_WriteField环境
	ter_breakpoints[2] = (Breakpoint){
        .source = tersafetsadd28,
        .target = tersafetsadd28ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	

	/*
	//0x1E1E28
	ter_breakpoints[4] = (Breakpoint){
        .source = tersafetsadd25,
        .target = tersafetsadd25ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };

	ter_breakpoints[5] = (Breakpoint){
        .source = tersafetsadd32,
        .target = tersafetsadd32ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/
	

	/*
	ter_breakpoints[5] = (Breakpoint){
        .source = tersafetsadd28,
        .target = tersafetsadd28ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };

	*/

	/*
	//sub_1000475C8
	ter_breakpoints[5] = (Breakpoint){
        .source = zhuxianchenghjadd1,
        .target = zhuxianchenghjadd1ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	/*
	ter_breakpoints[6] = (Breakpoint){
        .source = tersafetsadd21,
        .target = tersafetsadd21ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };

	ter_breakpoints[7] = (Breakpoint){
        .source = tersafetsadd22,
        .target = tersafetsadd22ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };

	ter_breakpoints[8] = (Breakpoint){
        .source = tersafetsadd23,
        .target = tersafetsadd23ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/
	

	ter_breakpoint_count = 6;
	

	//g_breakpoint_count = 3;
	//ter_breakpoint_count = 6;
	
	
	// 启动异常处理线程 拉闸30天
    pthread_t thread;
    pthread_create(&thread, NULL, exception_handler_thread, NULL);
    pthread_detach(thread);
	
	
    // 设置硬件断点

	//while(!isover100)
	while(true)
	{
    	setup_all_breakpoints();
		ensurereporter();
	}


	
}

void initbreakpoint_smoba()
{
	NSLog(@"小罪ADD: initbreakpoint_smoba: loaded, setting up hardware breakpoint...");

	NSLog(@"小罪ADD: initbreinitbreakpoint_smobaakpoint: jump_hook dylib loaded");

	mach_vm_address_t kaijuxieruadd   = Imageaddress + 0xA4E0FE0;
	mach_vm_address_t kaijuxieruaddret   = Imageaddress + 0xA4E0FE4;

	mach_vm_address_t shijujianceadd   = Imageaddress + 0x9AE9EF8;
	mach_vm_address_t shijujianceaddret = (mach_vm_address_t)hooked_ret0;

	mach_vm_address_t shijujianceadd2   = Imageaddress + 0x9AE9F98;
	mach_vm_address_t shijujianceadd2ret = Imageaddress + 0x9AE9FA8;

	mach_vm_address_t tersafetsadd1 = tersafeadd + 0xAA880;// 控制检测开关
	mach_vm_address_t tersafetsadd1ret = tersafeadd + 0xAA884;//

	mach_vm_address_t tersafetsadd2 = tersafeadd + 0x6CF8;// 环境检测
	mach_vm_address_t tersafetsadd2ret = (mach_vm_address_t)hooked_ret0;

	mach_vm_address_t tersafetsadd3 = tersafeadd + 0x210EAC;// ReportQueue_Enqueue
	mach_vm_address_t tersafetsadd3ret = (mach_vm_address_t)hooked_ret0;

	mach_vm_address_t tersafetsadd4 = tersafeadd + 0x582A4;//下发
	mach_vm_address_t tersafetsadd4ret = (mach_vm_address_t)hooked_sub_585D0;

	mach_vm_address_t tersafetsadd5 = tersafeadd + 0x2132C8;//VM_DispatchPendingCallbacks
	mach_vm_address_t tersafetsadd5ret = (mach_vm_address_t)hooked_ret0;

	mach_vm_address_t tersafetsadd6 = tersafeadd + 0x93C10;//闪退
	mach_vm_address_t tersafetsadd6ret = tersafeadd + 0x93C30;

	g_breakpoints[0] = (Breakpoint){
        .source = kaijuxieruadd,
        .target = kaijuxieruaddret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };

	/*
	g_breakpoints[1] = (Breakpoint){
        .source = shijujianceadd,
        .target = shijujianceaddret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	*/

	g_breakpoints[1] = (Breakpoint){
        .source = shijujianceadd2,
        .target = shijujianceadd2ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };

	//0x6CF8 环境检测
	g_breakpoints[2] = (Breakpoint){
        .source = tersafetsadd2,
        .target = tersafetsadd2ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };

	//0x210EAC ReportQueue_Enqueue
	g_breakpoints[3] = (Breakpoint){
        .source = tersafetsadd3,
        .target = tersafetsadd3ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };

	//0x2132C8 VM_DispatchPendingCallbacks
	g_breakpoints[4] = (Breakpoint){
        .source = tersafetsadd5,
        .target = tersafetsadd5ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };

	//0x93C10 闪退
	g_breakpoints[5] = (Breakpoint){
        .source = tersafetsadd6,
        .target = tersafetsadd6ret,
        .s0_val = 29.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };

    g_breakpoint_count = 6;

	//0xAA880 控制检测开关
	ter_breakpoints[0] = (Breakpoint){
        .source = tersafetsadd1,
        .target = tersafetsadd1ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };

	//0x6CF8 环境检测
	ter_breakpoints[1] = (Breakpoint){
        .source = tersafetsadd2,
        .target = tersafetsadd2ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };

	//0x210EAC ReportQueue_Enqueue
	ter_breakpoints[2] = (Breakpoint){
        .source = tersafetsadd3,
        .target = tersafetsadd3ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
		.d0_val = (double)1.0,
        .used = 1,
        .hw_index = -1
    };

	//0x582A4 下发
	ter_breakpoints[3] = (Breakpoint){
        .source = tersafetsadd4,
        .target = tersafetsadd4ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };

	//0x2132C8 VM_DispatchPendingCallbacks
	ter_breakpoints[4] = (Breakpoint){
        .source = tersafetsadd5,
        .target = tersafetsadd5ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };

	//0x93C10 闪退
	ter_breakpoints[5] = (Breakpoint){
        .source = tersafetsadd6,
        .target = tersafetsadd6ret,
        .s0_val = 0.0f,
        .s1_val = 0.0f,
        .used = 1,
        .hw_index = -1
    };
	
	ter_breakpoint_count = 6;

	
	// 启动异常处理线程
    pthread_t thread;
    pthread_create(&thread, NULL, exception_handler_thread_smoba, NULL);
    pthread_detach(thread);
	
    // 设置硬件断点

	//while(!isover100)
	while(true)
	{
    	setup_all_breakpoints();
	}


	
}

// 定义原函数类型
typedef kern_return_t (*task_get_exception_ports_t)(
    task_t task,
    exception_mask_t exception_mask,
    exception_mask_array_t masks,
    mach_msg_type_number_t *masksCnt,
    exception_port_array_t ports,
    exception_behavior_array_t behaviors,
    thread_state_flavor_array_t flavors
);

typedef kern_return_t (*task_get_special_port_t)(
    task_t task,
    int which_port,
    mach_port_t *special_port
);

// 全局原函数指针
static task_get_exception_ports_t original_task_get_exception_ports = NULL;
static task_get_special_port_t original_task_get_special_port = NULL;

kern_return_t replaced_task_get_exception_ports(
    task_t task,
    exception_mask_t exception_mask,
    exception_mask_array_t masks,
    mach_msg_type_number_t *masksCnt,
    exception_port_array_t ports,
    exception_behavior_array_t behaviors,
    thread_state_flavor_array_t flavors)
{
	//NSLog(@"小罪ADD: systemhook: replaced_task_get_exception_ports call!");
	//NSLog(@"小罪ADD: [+] replaced_task_get_exception_ports called. Stack trace:\n%@", [NSThread callStackSymbols]);
	//thread_suspend(mach_thread_self());
	
    // 调用原函数获取真实的异常端口配置
    kern_return_t kr = original_task_get_exception_ports(task, exception_mask, masks, masksCnt, ports, behaviors, flavors);
    if (kr == KERN_SUCCESS && masksCnt && *masksCnt > 0) {
        mach_msg_type_number_t new_count = 0;
        for (mach_msg_type_number_t i = 0; i < *masksCnt; i++) {
            // 如果掩码中包含 EXC_MASK_BREAKPOINT，则跳过该条目
            if (!(masks[i] & EXC_MASK_BREAKPOINT)) {
                if (new_count != i) 
				{
                    masks[new_count] = masks[i];
                    ports[new_count] = ports[i];
                    behaviors[new_count] = behaviors[i];
                    flavors[new_count] = flavors[i];
                }
                new_count++;
            }
			else
			{
				//NSLog(@"小罪ADD: systemhook: replaced_task_get_exception_ports :检测出调试端口");
				ports[i] = MACH_PORT_NULL;
				//NSLog(@"小罪ADD: [+] Hooked replaced_task_get_exception_ports called. Stack trace:\n%@", [NSThread callStackSymbols]);
			}
        }
        *masksCnt = new_count;
    }
    return kr;
}

kern_return_t replaced_task_get_special_port(
    task_t task,
    int which_port,
    mach_port_t *special_port)
{
	NSLog(@"小罪ADD: systemhook: replaced_task_get_special_port call!");
	NSLog(@"小罪ADD: [+] replaced_task_get_special_port called. Stack trace:\n%@", [NSThread callStackSymbols]);
	//kern_return_t kr = thread_suspend(mach_thread_self());
	
    // 如果是当前任务且请求的是 bootstrap 端口（which_port = 4）
    if (task == mach_task_self() && which_port == 4) 
	{
		// // 方式一：直接返回失败，反作弊将无法获取 bootstrap 端口
    	return original_task_get_special_port(task, which_port, special_port);
 
    }
	// 方式二：返回成功但端口为 MACH_PORT_NULL（需根据反作弊逻辑选择）
        // *special_port = MACH_PORT_NULL;
        // return KERN_SUCCESS;
	return KERN_FAILURE;
    
}



// ==================== 辅助函数：清除调试状态中的硬件断点 ====================

static void clear_hardware_breakpoints_in_state(thread_state_t state, mach_msg_type_number_t *stateCnt) {
    if (!state || !stateCnt || *stateCnt < ARM_DEBUG_STATE64_COUNT) {
        return;
    }
    
    // 强制转换为系统定义的调试状态结构体类型
    arm_debug_state64_t *debug_state = (arm_debug_state64_t *)state;
    
    // 清除所有硬件断点 (最多 16 个)
    for (int i = 0; i < 16; i++) {
        // 将控制寄存器的 ENABLE 位 (bit 0) 设为 0
        debug_state->__bcr[i] &= ~1;      // 禁用断点
        debug_state->__bvr[i] = 0;        // 清空地址
        
        // 同时清空观察点
        debug_state->__wcr[i] &= ~1;
        debug_state->__wvr[i] = 0;
    }
}

// ==================== Hook: thread_get_state ====================
// 拦截读取线程状态的调用，伪造无硬件断点的状态返回

kern_return_t replaced_thread_get_state(
    thread_act_t target_thread,
    thread_state_flavor_t flavor,
    thread_state_t old_state,
    mach_msg_type_number_t *old_stateCnt)
{
    // 调用原函数获取真实状态
    kern_return_t kr = original_thread_get_state(target_thread, flavor, old_state, old_stateCnt);
	
    
    if (kr == KERN_SUCCESS && flavor == ARM_DEBUG_STATE64) 
	{
        // 如果是读取调试状态，清除所有硬件断点信息
		//NSLog(@"小罪ADD: systemhook: replaced_thread_get_state :检测出正在读取ARM_DEBUG_STATE64");
		//NSLog(@"小罪ADD: [+] Hooked replaced_thread_get_state called. Stack trace:\n%@", [NSThread callStackSymbols]);
        clear_hardware_breakpoints_in_state(old_state, old_stateCnt);
		//thread_suspend(target_thread);
    }
    
    return kr;
}

// 定义原函数类型
typedef void (*dispatch_once_func_t)(dispatch_once_t *predicate, dispatch_block_t block);

// 保存原始函数指针
static dispatch_once_func_t original_dispatch_once = NULL;

static dispatch_once_func_t original_dispatch_once_kgvmp_dy = NULL;

void hooked_dispatch_once_kgvmp_dy(dispatch_once_t *predicate, dispatch_block_t block) 
{
	//long predicatelong = (long)predicate;
	//NSLog(@"小罪ADD: systemhook: 主线程 hooked_dispatch_once_kgvmp_dy called, passed predicateptr: 0x%p\n", (long)predicate);
	//NSLog(@"小罪ADD: [+] Hooked hooked_dispatch_once called. Stack trace:\n%@", [NSThread callStackSymbols]);
}

// 替换函数实现
void hooked_dispatch_once(dispatch_once_t *predicate, dispatch_block_t block) 
{
    
	long predicatelong = (long)predicate;
	long zuidi  = Imageaddress+0x13002950;
	//long zuigao = Imageaddress+0x130029FF;
	long zuigao = Imageaddress+0x130029FF;

	
	//if(predicate == (dispatch_once_t *)(Imageaddress+0x13002958))
	//if(predicatelong >= zuidi && predicatelong<= zuigao)

	if(
		//predicatelong == (Imageaddress+0x13002658) || //[_MidasIAPSecUtility sharedUtil]
		//predicatelong == (Imageaddress+0x13D4DE80) || //[RMLeakChecker getInstance]
		//predicatelong == (Imageaddress+0x13D4DF38)  //[RMReportCenter report:result:]

		
		predicatelong == (Imageaddress+0x13D641E0) ||
		predicatelong == (Imageaddress+0x13D55018) ||
		//predicatelong == (Imageaddress+0x13D4D9F0) ||
		predicatelong == (Imageaddress+0x13D4D9B8) ||
		predicatelong == (Imageaddress+0x13D4D730) ||
		predicatelong == (Imageaddress+0x13D4D920) ||
		predicatelong == (Imageaddress+0x13D4D710) ||
		predicatelong == (Imageaddress+0x13D4D978) ||
		predicatelong == (Imageaddress+0x13D4D8E0) ||
		predicatelong == (Imageaddress+0x13D4D8F8) ||
		predicatelong == (Imageaddress+0x13D4D778) ||

		predicatelong == (Imageaddress+0x13D4D630) ||
		predicatelong == (Imageaddress+0x13D4D980) ||
		predicatelong == (Imageaddress+0x13D4DF38) ||
		predicatelong == (Imageaddress+0x13D4DCE0) ||
		predicatelong == (Imageaddress+0x13D4DEA0) ||
		predicatelong == (Imageaddress+0x13D4D470) ||

		predicatelong == (Imageaddress+0x13D4D468) ||
		predicatelong == (Imageaddress+0x13D4D230) ||
		predicatelong == (Imageaddress+0x13D4D4C8) ||
		predicatelong == (Imageaddress+0x13D4D170) ||
		predicatelong == (Imageaddress+0x13D4D458) ||
		predicatelong == (Imageaddress+0x13D4CED8) ||
		predicatelong == (Imageaddress+0x13D4CEC8) ||
		predicatelong == (Imageaddress+0x13D76178) ||
		predicatelong == (Imageaddress+0x13D76320) ||
		predicatelong == (Imageaddress+0x13D76218) ||
		predicatelong == (Imageaddress+0x13D76018) ||
		predicatelong == (Imageaddress+0x13D4D948) ||
		predicatelong == (Imageaddress+0x13D4D360) ||
		predicatelong == (Imageaddress+0x13D4D238) ||
		predicatelong == (Imageaddress+0x13D4D360) ||
		predicatelong == (Imageaddress+0x13D76080) 
	

	)
	{
		NSLog(@"小罪ADD: systemhook: 主线程 hooked_dispatch_once called, passed predicateptr: 0x%p\n", (long)predicate - Imageaddress);
		NSLog(@"小罪ADD: [+] Hooked hooked_dispatch_once called. Stack trace:\n%@", [NSThread callStackSymbols]);

	}
	else
	{
		//NSLog(@"小罪ADD: systemhook: 主线程hooked_dispatch_once 登录sdk触发！ predicate: %p\n", predicate);
		 // 调用原始实现
	    if (original_dispatch_once) 
		{
	        original_dispatch_once(predicate, block);
	    } else {
	        // 如果原始指针无效，直接调用系统函数
	        dispatch_once(predicate, block);
	    }
	}
	

}

#include <stdio.h>
#include <stdlib.h>
typedef uint64_t (*GetDataFromTGPAFunc)(uint64_t,uint64_t);

// 保存原始函数指针
static GetDataFromTGPAFunc original_GetDataFromTGPA = NULL;

static uint64_t myGetDataFromTGPAdata;

// 替换函数实现
uint64_t hooked_GetDataFromTGPA(uint64_t a1,uint64_t a2) 
{
	NSLog(@"小罪ADD: systemhook: 主线程hooked_GetDataFromTGPA called,a1=0x%llx,a2=0x%llx",a1,a2);

	uint64_t caller_return_address = (uint64_t)__builtin_return_address(0);

	NSLog(@"小罪ADD: systemhook: 主线程hooked_GetDataFromTGPA caller_return_address: 0x%llx , ptr: 0x%llx",caller_return_address,caller_return_address-Imageaddress);

	NSLog(@"小罪ADD: [+] Hooked hooked_GetDataFromTGPA called. Stack trace:\n%@", [NSThread callStackSymbols]);

	myGetDataFromTGPAdata = (uint64_t)original_GetDataFromTGPA(a1,a2);

	if(myGetDataFromTGPAdata)
	{
		size_t DataFromTGPAsize = strlen((const char*)myGetDataFromTGPAdata);
		NSLog(@"小罪ADD: [+] Hooked hooked_GetDataFromTGPA DataFromTGPAsize:%d,myGetDataFromTGPAdata =%llx",DataFromTGPAsize,myGetDataFromTGPAdata);
		if(DataFromTGPAsize >= 0x81)//129
		{
			memset((void*)(myGetDataFromTGPAdata + 0x50), 0, 0x31);
			NSLog(@"小罪ADD: systemhook: 主线程hooked_GetDataFromTGPA DataFromTGPAsize >= 0x81,memset called!");
		}
	}
	

	/*
	if(!myGetDataFromTGPAdata)
	{
		vm_address_t address = 0;
	    vm_size_t size = 0x1024;//0x2000;
	    int flags  = VM_FLAGS_ANYWHERE;
	    kern_return_t kr  = vm_allocate(mach_task_self (),&address,size,flags);
		if(kr == KERN_SUCCESS)
	    {
			vm_protect(mach_task_self (), address, 0x1024, false, VM_PROT_READ|VM_PROT_WRITE);
			memset((void*)address, 0, 0x1024);
			NSLog(@"小罪ADD:  hooked_GetDataFromTGPA申请myGetDataFromTGPAdata内存：%p", address);
		}
		myGetDataFromTGPAdata = (uint64_t)address;
	}
	*/

	
	return myGetDataFromTGPAdata;
	
	//return 0;
    //printf("[HOOK] _GetDataFromTGPA called\n");
    
    // 可选：添加自定义逻辑
    // 调用原始函数
    //__int64 result = original_GetDataFromTGPA ? original_GetDataFromTGPA() : 0;
    
    //printf("[HOOK] _GetDataFromTGPA returned: %lld\n", result);
    //return result;
}

typedef uint64_t (*InitTGPAFunc)();
static InitTGPAFunc original_InitTGPA = NULL;
// 替换函数实现
uint64_t hooked_InitTGPA() 
{
    NSLog(@"小罪ADD: systemhook: 主线程 hooked_InitTGPA called");
	NSLog(@"小罪ADD: [+] Hooked hooked_InitTGPA called. Stack trace:\n%@", [NSThread callStackSymbols]);

    return 0;
}


typedef id (*OriginalInitMainFlowFunc)(void *a1, const char *a2, ...);
// 保存原始函数指针
static OriginalInitMainFlowFunc original_startInitMainFlow_reprovideDelegate = NULL;

id hooked_startInitMainFlow_reprovideDelegate(void *a1, const char *a2, ...)
{
	NSLog(@"小罪ADD: systemhook: 主线程 hooked_Inhooked_startInitMainFlow_reprovideDelegateitTGPA called");
	NSLog(@"小罪ADD: [+] Hooked hooked_startInitMainFlow_reprovideDelegate called. Stack trace:\n%@", [NSThread callStackSymbols]);
    return 0;
}

typedef int (*proc_regionfilename_t)(int pid, uint64_t address, char *buf, uint32_t buf_size);
proc_regionfilename_t orig_proc_regionfilename = NULL;

// Hook 函数实现
int hooked_proc_regionfilename(int pid, uint64_t address, char *buf, uint32_t buf_size) {
    // 如果 buf 为空，直接调用原函数
    if (!buf || buf_size == 0) {
        return orig_proc_regionfilename(pid, tersafeadd, buf, buf_size);
    }


    // 关键逻辑：检查 address 是否属于你想隐藏的模块
    Dl_info info;
    if (dladdr((void *)address, &info) && info.dli_fname) {
        // 匹配需要隐藏的模块路径
        //if (strcmp(info.dli_fname, HIDE_PATH) == 0) 
		if(strstr(info.dli_fname, "libswiftPrivate_BiomeStreams") != NULL)
		{
			NSLog(@"小罪ADD: systemhook: 主线程 hooked_proc_regionfilename called");
			NSLog(@"小罪ADD: [+] Hooked hooked_proc_regionfilename called. Stack trace:\n%@", [NSThread callStackSymbols]);
			return orig_proc_regionfilename(pid, tersafeadd, buf, buf_size);
        }
    }

    // 默认情况，调用原函数
    return orig_proc_regionfilename(pid, address, buf, buf_size);
}

typedef uint64_t (*TssSDKGetReportDataFunc)();
static TssSDKGetReportDataFunc original_TssSDKGetReportData = NULL;
static TssSDKGetReportDataFunc original_TssSDKGetReportData2 = NULL;
static TssSDKGetReportDataFunc original_TssSDKGetReportData3 = NULL;

// 替换函数实现
uint64_t hooked_TssSDKGetReportData() 
{
    NSLog(@"小罪ADD: systemhook: 主线程 hooked_TssSDKGetReportData called");
	NSLog(@"小罪ADD: [+] Hooked hooked_TssSDKGetReportData called. Stack trace:\n%@", [NSThread callStackSymbols]);

    return 0;
}

uint64_t hooked_TssSDKGetReportData2() 
{
    NSLog(@"小罪ADD: systemhook: 主线程 hooked_TssSDKGetReportData called");
	NSLog(@"小罪ADD: [+] Hooked hooked_TssSDKGetReportData called. Stack trace:\n%@", [NSThread callStackSymbols]);

    return 0;
}

uint64_t hooked_TssSDKGetReportData3() 
{
    NSLog(@"小罪ADD: systemhook: 主线程 hooked_TssSDKGetReportData called");
	NSLog(@"小罪ADD: [+] Hooked hooked_TssSDKGetReportData called. Stack trace:\n%@", [NSThread callStackSymbols]);

    return 0;
}

typedef uint64_t (*ReportQueueFunc)(uint64_t,uint64_t);
static ReportQueueFunc original_ReportQueue = NULL;

uint64_t hooked_ReportQueue(uint64_t x0,uint64_t x1) 
{
		
		int opcode = Read_Int(x1);
		NSString *result = @"0";

		if(opcode < 0x100) result = @"小于0x100未的知异常";
		if(opcode >= 0x100 && opcode < 0x200) result = @"VM执行引擎异常、调试检测";
		if(opcode >= 0x200 && opcode < 0x300) result = @"Inline Hook / 代码完整性 / Session管理";
		if(opcode >= 0x300 && opcode < 0x400) result = @"VM opcode参数非法";
		if(opcode >= 0x400 && opcode < 0x500) result = @"VM opcode未知分支";
		if(opcode >= 0x500 && opcode < 0x600) result = @"定时器/调度系统异常";
		if(opcode >= 0x600 && opcode < 0x700) result = @"dladdr/内存映射异常";
		if(opcode >= 0x700 && opcode < 0x800) result = @"文件系统异常";
		if(opcode >= 0x800) result = @"超过0x800的未知异常";

		NSLog(@"小罪ADD: hooked_ReportQueue: 通道异常上报触发,opcode:%d,异常状态：%@",opcode,result);
			
				
}

typedef unsigned int (*sleep_func_t)(unsigned int seconds);
sleep_func_t orig_sleep = NULL;

// 自定义的替换函数
unsigned int hooked_sleep(unsigned int seconds) 
{
	uint64_t caller_return_address = (uint64_t)__builtin_return_address(0);

	if(caller_return_address == (uint64_t)(tersafeadd + 0x2138f4))
	{
		mach_port_t mach_port = mach_thread_self();
		pthread_t pthread = pthread_from_mach_thread_np(mach_port);

		char name[256] = {0};
	
		NSLog(@"小罪ADD: systemhook: ter线程 hooked_sleep called");
		int result = pthread_getname_np(pthread, name, sizeof(name));
		if (result == 0 && strlen(name) > 0)
		{
			NSLog(@"小罪ADD: systemhook: ter线程 hooked_sleep called: threadname:%s",name);
		}
		
	
		NSLog(@"小罪ADD: systemhook: hooked_sleep caller_return_address: 0x%llx , ptr: 0x%llx",caller_return_address,caller_return_address-tersafeadd);
	
		NSLog(@"小罪ADD: [+] Hooked hooked_sleep called. Stack trace:\n%@", [NSThread callStackSymbols]);
	
		kern_return_t kr = thread_suspend(mach_thread_self());

		return 0;
	}


    //printf("[Dobby Hook] sleep(%u) called\n", seconds);
    
    // 可以修改参数，例如强制睡眠时间减半
    // seconds = seconds / 2;
    
    // 调用原函数
    unsigned int ret = orig_sleep(seconds);

    // 可以修改返回值，例如强制返回 0
    //return 0;
    return ret;
}

// 1. 声明原函数类型和用于保存原函数地址的指针
typedef void (*abort_func_t)(void);
abort_func_t orig_abort = NULL;

// 2. 自定义的替换函数
void hooked_abort(void) {
    // 在这里做你想做的事，比如记录日志
    
	NSLog(@"小罪ADD: hooked_abort called!取消");
	NSLog(@"小罪ADD: [+] Hooked hooked_abort called. Stack trace:\n%@", [NSThread callStackSymbols]);

    // 关键：不要调用 orig_abort()，这样程序就不会真正终止

    // 你可以在这里添加其他处理逻辑，例如调用 exit(0) 来正常退出
    // exit(0);
}

typedef void (*_dispatch_once_f_t)(dispatch_once_t *predicate, void *context, dispatch_function_t function);
static _dispatch_once_f_t orig__dispatch_once_f = NULL;

// 自定义替换函数
void hooked__dispatch_once_f(dispatch_once_t *predicate, void *context, dispatch_function_t function) {
    // 获取当前调用地址（用于调试/日志）
    void *caller = __builtin_return_address(0);
    
    // 可选：记录日志，不影响原逻辑
    NSLog(@"小罪ADD: [Dobby Hook] hooked__dispatch_once_f called, predicate=%p, context=%p, func=%p, caller=%p\n",
           predicate, context, function, caller);
    
    // **关键**：虽然我们拦截了调用，但必须调用原函数以保证单例机制正常工作
    // 如果不调用原函数，单例代码永远不会执行，可能导致状态未初始化而崩溃
    if (orig__dispatch_once_f) {
        //orig__dispatch_once_f(predicate, context, function);
    }
}

typedef void (*_dispatch_sync_t)(dispatch_queue_t queue, dispatch_block_t block);
static _dispatch_sync_t orig__dispatch_sync = NULL;

// 自定义替换函数
void hooked__dispatch_sync(dispatch_queue_t queue, dispatch_block_t block) {
    // 获取当前调用地址
    void *caller = __builtin_return_address(0);
    
    // 获取队列标签（可选，用于调试）
    const char *queue_label = dispatch_queue_get_label(queue);
    
     NSLog(@"小罪ADD: [Dobby Hook] hooked__dispatch_sync called, queue=%p (%s), block=%p, caller=%p\n",
           queue, queue_label ? queue_label : "unknown", block, caller);
    
    // 默认情况下调用原函数，确保原有同步逻辑正常工作
    // 可以根据条件决定是否调用原函数，例如：
    // if (some_condition) {
    //     orig__dispatch_sync(queue, block);
    // } else {
    //     // 直接在当前线程执行 block，绕过同步机制
    //     block();
    // }
    if (orig__dispatch_sync) {
        //orig__dispatch_sync(queue, block);
    }
}

typedef void (*_dispatch_async_t)(dispatch_queue_t queue, dispatch_block_t block);
static _dispatch_async_t orig__dispatch_async = NULL;

void hooked__dispatch_async(dispatch_queue_t queue, dispatch_block_t block) {
    // 获取调用者的返回地址，用于调试或日志分析
    void *caller = __builtin_return_address(0);
    const char *queue_label = dispatch_queue_get_label(queue);
    
    NSLog(@"小罪ADD: [Dobby Hook] hooked__dispatch_async called, queue=%p (%s), block=%p, caller=%p\n",
           queue, queue_label ? queue_label : "unknown", block, caller);
    
    // 3. 调用原始的 _dispatch_async 函数，以维持 GCD 的正常工作机制
    if (orig__dispatch_async) {
        //orig__dispatch_async(queue, block);
    } else {
        // 如果原函数指针无效，可以选择直接执行 block，以避免逻辑丢失
        if (block) {
            block();
        }
    }
}


//入口
__attribute__((constructor)) static void initializer(void)
{	
/***** roothide specific ****/
	roothide_init();
/***** roothide specific ****/

if (load_executable_path() == 0) 
{

	if (string_has_suffix(gExecutablePath, "/smoba")) 
	{
		NSLog(@"小罪ADD: systemhook: smoba 启动！：%s", gExecutablePath);

		gFullyDebugged = true;
		if (jbclient_process_checkin(&JB_RootPath, &JB_BootUUID, &JB_SandboxExtensions, &gFullyDebugged) == 0) 
		{
			//consume_tokenized_sandbox_extensions(JB_SandboxExtensions);
		}

		NSLog(@"小罪ADD: systemhook: smoba jbclient_process_checkin：JB_RootPath:%s,JB_BootUUID:%s,JB_SandboxExtensions:%s,gFullyDebugged:%d", JB_RootPath, JB_BootUUID, JB_SandboxExtensions, gFullyDebugged);

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

		// Hook task_get_exception_ports
   		int ret = DobbyHook((void *)task_get_exception_ports,(void *)replaced_task_get_exception_ports, (void **)&original_task_get_exception_ports);
		NSLog(@"小罪ADD: [Dobby] hook task_get_exception_ports: %s", ret == 0 ? "success" : "failed");
		
    	// Hook task_get_special_port
    	//ret = DobbyHook((void *)task_get_special_port, (void *)replaced_task_get_special_port, (void **)&original_task_get_special_port);
		//NSLog(@"小罪ADD: [Dobby] hook task_get_special_port: %s", ret == 0 ? "success" : "failed");

		// Hook thread_get_state
    	ret = DobbyHook((void *)thread_get_state, (void *)replaced_thread_get_state,(void **)&original_thread_get_state);
		NSLog(@"小罪ADD: [Dobby] hook thread_get_state: %s", ret == 0 ? "success" : "failed");

		
		ret = DobbyHook((void *)stat, (void *)hooked_stat, (void **)&orig_stat);
        NSLog(@"小罪ADD: [Dobby] hook stat: %s", ret == 0 ? "success" : "failed");

		ret = DobbyHook((void *)access, (void *)hooked_access, (void **)&orig_access);
        NSLog(@"小罪ADD: [Dobby] hook access: %s", ret == 0 ? "success" : "failed");

		// rename
        ret = DobbyHook((void *)rename, (void *)hooked_rename, (void **)&orig_rename);
        NSLog(@"小罪ADD: [Dobby] hook rename: %s", ret == 0 ? "success" : "failed");

		ret = DobbyHook((void *)open, (void *)hooked_open, (void **)&orig_open);
        NSLog(@"小罪ADD: [Dobby] hook open: %s", ret == 0 ? "success" : "failed");

		// 环境变量
        ret = DobbyHook((void *)getenv, (void *)hooked_getenv, (void **)&orig_getenv);
        NSLog(@"小罪ADD: [Dobby] hook getenv: %s", ret == 0 ? "success" : "failed");

		ret = DobbyHook((void *)lstat, (void *)hooked_lstat, (void **)&orig_lstat);
        NSLog(@"小罪ADD: [Dobby] hook lstat: %s", ret == 0 ? "success" : "failed");

		ret = DobbyHook((void *)fopen, (void *)hooked_fopen, (void **)&orig_fopen);
        NSLog(@"小罪ADD: [Dobby] hook fopen: %s", ret == 0 ? "success" : "failed");

		// mkdir
        ret = DobbyHook((void *)mkdir, (void *)hooked_mkdir, (void **)&orig_mkdir);
        NSLog(@"小罪ADD: [Dobby] hook mkdir: %s", ret == 0 ? "success" : "failed");

		// rmdir
        ret = DobbyHook((void *)rmdir, (void *)hooked_rmdir, (void **)&orig_rmdir);
        NSLog(@"小罪ADD: [Dobby] hook rmdir: %s", ret == 0 ? "success" : "failed");

		//ret = DobbyHook((void *)dladdr, (void *)hooked_dladdr, (void **)&orig_dladdr); //这个好像也会直接三方
		//NSLog(@"小罪ADD: [Dobby] hook dladdr: %s", ret == 0 ? "success" : "failed");
		

		ret = DobbyHook((void *)proc_regionfilename, (void *)hooked_proc_regionfilename, (void **)&orig_proc_regionfilename);
		NSLog(@"小罪ADD: [Dobby] hook proc_regionfilename: %s", ret == 0 ? "success" : "failed");
		
		
		// ---------- 使用 runtime Hook Objective-C 方法 ----------
		// NSFileManager fileExistsAtPath
        Method m1 = class_getInstanceMethod([NSFileManager class], @selector(fileExistsAtPath:));
        orig_fileExistsAtPath = method_getImplementation(m1);
        method_setImplementation(m1, (IMP)hooked_fileExistsAtPath);
		

		//smobainit();
		pthread_t thread3;
    	pthread_create(&thread3, NULL, smobainit, NULL);

				
		return;

		
	}


		
	if (string_has_suffix(gExecutablePath, "/DeltaForceClient")) 
	{
		NSLog(@"小罪ADD: systemhook: DeltaForceClient 启动！：%s", gExecutablePath);

		issjz = true;

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

		// Hook task_get_exception_ports
   		int ret = DobbyHook((void *)task_get_exception_ports,(void *)replaced_task_get_exception_ports, (void **)&original_task_get_exception_ports);
		NSLog(@"小罪ADD: [Dobby] hook task_get_exception_ports: %s", ret == 0 ? "success" : "failed");
		
    	// Hook task_get_special_port
    	//ret = DobbyHook((void *)task_get_special_port, (void *)replaced_task_get_special_port, (void **)&original_task_get_special_port);
		//NSLog(@"小罪ADD: [Dobby] hook task_get_special_port: %s", ret == 0 ? "success" : "failed");

		// Hook thread_get_state
    	ret = DobbyHook((void *)thread_get_state, (void *)replaced_thread_get_state,(void **)&original_thread_get_state);
		NSLog(@"小罪ADD: [Dobby] hook thread_get_state: %s", ret == 0 ? "success" : "failed");

		
		ret = DobbyHook((void *)stat, (void *)hooked_stat, (void **)&orig_stat);
        NSLog(@"小罪ADD: [Dobby] hook stat: %s", ret == 0 ? "success" : "failed");

		ret = DobbyHook((void *)access, (void *)hooked_access, (void **)&orig_access);
        NSLog(@"小罪ADD: [Dobby] hook access: %s", ret == 0 ? "success" : "failed");

		// rename
        ret = DobbyHook((void *)rename, (void *)hooked_rename, (void **)&orig_rename);
        NSLog(@"小罪ADD: [Dobby] hook rename: %s", ret == 0 ? "success" : "failed");

		ret = DobbyHook((void *)open, (void *)hooked_open, (void **)&orig_open);
        NSLog(@"小罪ADD: [Dobby] hook open: %s", ret == 0 ? "success" : "failed");

		// 环境变量
        ret = DobbyHook((void *)getenv, (void *)hooked_getenv, (void **)&orig_getenv);
        NSLog(@"小罪ADD: [Dobby] hook getenv: %s", ret == 0 ? "success" : "failed");

		ret = DobbyHook((void *)lstat, (void *)hooked_lstat, (void **)&orig_lstat);
        NSLog(@"小罪ADD: [Dobby] hook lstat: %s", ret == 0 ? "success" : "failed");

		ret = DobbyHook((void *)fopen, (void *)hooked_fopen, (void **)&orig_fopen);
        NSLog(@"小罪ADD: [Dobby] hook fopen: %s", ret == 0 ? "success" : "failed");

		// mkdir
        ret = DobbyHook((void *)mkdir, (void *)hooked_mkdir, (void **)&orig_mkdir);
        NSLog(@"小罪ADD: [Dobby] hook mkdir: %s", ret == 0 ? "success" : "failed");

		// rmdir
        ret = DobbyHook((void *)rmdir, (void *)hooked_rmdir, (void **)&orig_rmdir);
        NSLog(@"小罪ADD: [Dobby] hook rmdir: %s", ret == 0 ? "success" : "failed");

		//ret = DobbyHook((void *)dladdr, (void *)hooked_dladdr, (void **)&orig_dladdr); //这个好像也会直接三方
		//NSLog(@"小罪ADD: [Dobby] hook dladdr: %s", ret == 0 ? "success" : "failed");
		

		ret = DobbyHook((void *)proc_regionfilename, (void *)hooked_proc_regionfilename, (void **)&orig_proc_regionfilename);
		NSLog(@"小罪ADD: [Dobby] hook proc_regionfilename: %s", ret == 0 ? "success" : "failed");
		
		
		// ---------- 使用 runtime Hook Objective-C 方法 ----------
		// NSFileManager fileExistsAtPath
        Method m1 = class_getInstanceMethod([NSFileManager class], @selector(fileExistsAtPath:));
        orig_fileExistsAtPath = method_getImplementation(m1);
        method_setImplementation(m1, (IMP)hooked_fileExistsAtPath);
		
		
		/*
		//NSFileManager fileExistsAtPath:isDirectory
        Method m2 = class_getInstanceMethod([NSFileManager class], @selector(fileExistsAtPath:isDirectory:));
        orig_fileExistsAtPath_isDirectory = method_getImplementation(m2);
        method_setImplementation(m2, (IMP)hooked_fileExistsAtPath_isDirectory);

		//UIApplication canOpenURL
        Method m3 = class_getInstanceMethod([UIApplication class], @selector(canOpenURL:));
        orig_canOpenURL = method_getImplementation(m3);
        method_setImplementation(m3, (IMP)hooked_canOpenURL);
		*/

		while(!Imageaddress)
		{
			Imageaddress = Get_Imageaddress_base();
		}

		while(!tersafeadd)
		{
			tersafeadd = Get_tersafe_base();
		}

		long kgvmp_dyadd = 0;
		while(!kgvmp_dyadd)
		{
			kgvmp_dyadd = Get_kgvmp_dy_base();
		}

		//void *dispatch_once_ptr = (void *)(Imageaddress+0xE3B6338);
		//ret = DobbyHook(dispatch_once_ptr, (void *)hooked_dispatch_once, (void **)&original_dispatch_once);
		//NSLog(@"小罪ADD: [Dobby] hook dispatch_once_ptr: %s", ret == 0 ? "success" : "failed");

		void *startInitMainFlow_reprovideDelegate_ptr = (void *)(Imageaddress+0xE3BCCC0);
		ret = DobbyHook(startInitMainFlow_reprovideDelegate_ptr, (void *)hooked_startInitMainFlow_reprovideDelegate, (void **)&original_startInitMainFlow_reprovideDelegate);
		NSLog(@"小罪ADD: [Dobby] hook startInitMainFlow_reprovideDelegate_ptr: %s", ret == 0 ? "success" : "failed");

		/*
		void *GetDataFromTGPA_ptr = (void *)(Imageaddress+0xE3B4F40);
		ret = DobbyHook(GetDataFromTGPA_ptr, (void *)hooked_GetDataFromTGPA, (void **)&original_GetDataFromTGPA);
		NSLog(@"小罪ADD: [Dobby] hook GetDataFromTGPA_ptr: %s", ret == 0 ? "success" : "failed");

		void *InitTGPA_ptr = (void *)(Imageaddress+0xE3B4F4C);
		ret = DobbyHook(InitTGPA_ptr, (void *)hooked_InitTGPA, (void **)&original_InitTGPA);
		NSLog(@"小罪ADD: [Dobby] hook GetDataFromTGPA_ptr: %s", ret == 0 ? "success" : "failed");
		*/
		

		void * kgvmp_dy_dispatch_once_ptr = (void *)(kgvmp_dyadd+0xCFCE0);
		ret = DobbyHook(kgvmp_dy_dispatch_once_ptr, (void *)hooked_dispatch_once_kgvmp_dy, (void **)&original_dispatch_once_kgvmp_dy);
		NSLog(@"小罪ADD: [Dobby] hook kgvmp_dy_dispatch_once_ptr: %s", ret == 0 ? "success" : "failed");

		void * kgvmp_dy_dispatch_async_ptr = (void *)(kgvmp_dyadd+0xCFCC8);
		ret = DobbyHook(async_addr, (void *)hooked__dispatch_async, (void **)&orig__dispatch_async);
		NSLog(@"小罪ADD: [Dobby] hook kgvmp_dy_dispatch_async_ptr: %s", ret == 0 ? "success" : "failed");


		
		/*
		void *TssSDKGetReportData2_ptr = (void *)(Imageaddress+0xE3B4D90);
		ret = DobbyHook(TssSDKGetReportData2_ptr, (void *)hooked_TssSDKGetReportData2, (void **)&original_TssSDKGetReportData2);
		NSLog(@"小罪ADD: [Dobby] hook TssSDKGetReportData_ptr2: %s", ret == 0 ? "success" : "failed");

		void *TssSDKGetReportData_ptr = (void *)(Imageaddress+0xE3B4D84);
		
		void *TssSDKGetReportData3_ptr = (void *)(Imageaddress+0xE3B4D9C);

		ret = DobbyHook(TssSDKGetReportData_ptr, (void *)hooked_TssSDKGetReportData, (void **)&original_TssSDKGetReportData);
		NSLog(@"小罪ADD: [Dobby] hook TssSDKGetReportData_ptr: %s", ret == 0 ? "success" : "failed");

		ret = DobbyHook(TssSDKGetReportData3_ptr, (void *)hooked_TssSDKGetReportData3, (void **)&original_TssSDKGetReportData3);
		NSLog(@"小罪ADD: [Dobby] hook TssSDKGetReportData_ptr3: %s", ret == 0 ? "success" : "failed");
		*/

		/*
		void *ReportQueue_ptr = (void *)(tersafeadd+0x210EAC);
		ret = DobbyHook(ReportQueue_ptr, (void *)hooked_ReportQueue, (void **)&original_ReportQueue);
		NSLog(@"小罪ADD: [Dobby] hook ReportQueue_ptr: %s", ret == 0 ? "success" : "failed");
		*/

		
		void *sleep_ptr = (void *)(tersafeadd+0x249E90);
		ret = DobbyHook(sleep_ptr, (void *)hooked_sleep, (void **)&orig_sleep);
		NSLog(@"小罪ADD: [Dobby] hook sleep_ptr: %s", ret == 0 ? "success" : "failed");

		/*
		void *abort_addr = dlsym(RTLD_DEFAULT, "abort");
    	if (abort_addr) 
		{
			ret = DobbyHook(abort_addr, (void *)hooked_abort, (void **)&orig_abort);
			NSLog(@"小罪ADD: hook abort_addr: %s", ret == 0 ? "success" : "failed");
		}
		*/

		void *once_f_addr = (void *)(tersafeadd+0x249860);
		ret = DobbyHook(once_f_addr, (void *)hooked__dispatch_once_f, (void **)&orig__dispatch_once_f);
		NSLog(@"小罪ADD: [Dobby] hook once_f_addr: %s", ret == 0 ? "success" : "failed");

		void *sync_addr =(void *)(tersafeadd+0x249890);
		ret = DobbyHook(sync_addr, (void *)hooked__dispatch_sync, (void **)&orig__dispatch_sync);
		NSLog(@"小罪ADD: [Dobby] hook sync_addr: %s", ret == 0 ? "success" : "failed");


		loadandinitshare(); //26.3.21屏蔽

		
		//initbreakpoint();

		//pthread_t thread2;
        //pthread_create(&thread2, NULL, crchackthread, NULL);
	
		return;


		// stat64 (如果符号存在)
        void *stat64_addr = (void *)dlsym(RTLD_DEFAULT, "stat64");
        if (stat64_addr) {
            ret = DobbyHook(stat64_addr, (void *)hooked_stat64, (void **)&orig_stat64);
            NSLog(@"小罪ADD: [Dobby] hook stat64: %s", ret == 0 ? "success" : "failed");
        } else {
            NSLog(@"小罪ADD: [Dobby] stat64 not found, skipping");
        }
        
        
        
        
        
        

		//dyld
		
		//ret = DobbyHook((void *)_dyld_get_image_name, (void *)hooked_dyld_get_image_name, (void **)&orig_dyld_get_image_name); //会三方
        //NSLog(@"小罪ADD: [Dobby] hook _dyld_get_image_name: %s", ret == 0 ? "success" : "failed");

		ret = DobbyHook((void *)dlsym, (void *)hooked_dlsym, (void **)&orig_dlsym);
        NSLog(@"小罪ADD: [Dobby] hook dlsym: %s", ret == 0 ? "success" : "failed");

		

		

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
