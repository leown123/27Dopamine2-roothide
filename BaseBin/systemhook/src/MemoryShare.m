
#include "MemoryShare.h"

#include <fcntl.h>
#include <unistd.h>
#include <stdio.h>
//#include <iostream>
#include <sys/mman.h>

#import <Foundation/Foundation.h>

const char* sharePath = "/var/mobile/Library/SpringBoard/.ldata";

//size_t shareSize = 1024 * 30; // 30Kb共享空间

// 打开共享通道

void* openShareChannel(void)
{
    NSString *tmpDir = NSTemporaryDirectory();
    NSLog(@"小罪ADD: systemhook：openShareChannel 拟共享的tmp directory path: %@", tmpDir);
        
    // 示例：构建一个临时文件路径
    NSString *fileName = @".ldata";
    NSString *filePath = [tmpDir stringByAppendingPathComponent:fileName];
    NSLog(@"小罪ADD: systemhook：openShareChannel 拟共享的tmp file path: %@", filePath);

    size_t shareSize = sizeof(struct ShareStruct))*2;

    NSLog(@"小罪ADD: systemhook：openShareChannel shareSize: %d,oldshareSize: %d", shareSize,1024 * 30);

    // 可以将filePath传递给open函数使用
    // int fd = open([filePath UTF8String], O_CREAT | O_WRONLY, 0644);

    int fd = open([filePath UTF8String], O_RDWR | O_CREAT, 0777);

    NSLog(@"小罪ADD: systemhook：openShareChannel fd: %d", fd);
    
    if (fd < 0) {
        return (void*)-1;
    }
    // 如果文件不存在，创建文件
    if (ftruncate(fd, shareSize) < 0) {
        return (void*)-1;
    }
    // 修改用户组为mobile
    chown(sharePath, 501, 501);
    void* ptr = mmap(NULL, shareSize, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);

    NSLog(@"小罪ADD: systemhook：openShareChannel mmapptr: %lx", ptr);
    
    if (ptr == MAP_FAILED) {
        return (void*)-1;
    }
    return ptr;
}

// 关闭共享通道
void closeShareChannel(void* ptr) {
    munmap(ptr, shareSize);
}

// 同步共享通道
void syncShareChannel(void* ptr) {
    msync(ptr, shareSize, MS_SYNC);
}
