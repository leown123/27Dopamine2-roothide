
#include "MemoryShare.hpp"

#include <fcntl.h>
#include <unistd.h>
#include <stdio.h>
#include <iostream>
#include <sys/mman.h>



std::string sharePath = "/var/mobile/Library/SpringBoard/";

size_t shareSize = 1024 * 30; // 30Kb共享空间

// 打开共享通道

void* openShareChannel(std::string name) {
    int fd = open((sharePath + name).c_str(), O_RDWR | O_CREAT, 0777);
    if (fd < 0) {
        return (void*)-1;
    }
    // 如果文件不存在，创建文件
    if (ftruncate(fd, shareSize) < 0) {
        return (void*)-1;
    }
    // 修改用户组为mobile
    chown((sharePath + name).c_str(), 501, 501);
    void* ptr = mmap(NULL, shareSize, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
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
