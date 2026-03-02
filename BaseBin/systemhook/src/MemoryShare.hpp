
#ifndef MemoryShare_hpp
#define MemoryShare_hpp

#include <stdio.h>
#include <string>


void* openShareChannel(std::string name);
void closeShareChannel(void* ptr);
void syncShareChannel(void* ptr);



typedef struct {
    float x;
    float y;
} Vector2;

typedef struct {
    float x;
    float y;
    float z;
} Vector3;


struct Vector4D {
    float X, Y, W, H;
};


struct Vector {
    float X, Y, Z;
};

struct Rotator {
    float Pitch, Yaw, Roll;
};

struct MinimalViewInfo {
    Vector Location;
    Rotator Rotation;
    float FOV;
};

struct Rotation矩阵 {
    float _00, _01, _02; /*_03;*/
    float _10, _11, _12; /*_13;*/
    float _20, _21, _22; /*_23;*/
    // float _30, _31, _32 _33;
};

struct TeamComp {
    int TeamId;
    int CampId;
};

struct HealthSet {
    float Health;
    float HealthMax;
    float ImpendingDeathHealth;
    float MaxImpendingDeathHealth;
    float ArmorHealth;
    float MaxArmorHealth;
    float HelmetArmorHealth;
    float MaxHelmetArmorHealth;
};

typedef struct PlayerInfo {
    bool actived;
    
    int id;
    
    int GNameID;
    std::string GName;
    
    float MaxWalkSpeed;
    TeamComp TeamComp;
    
    float Health;
    float MaxHealth;
    
    Vector3 pos;
    Vector2 scrPosVec2;
    Vector4D scrPosVec4;
    float 对象距离;
    
    long WeaponID;
    int bIsFiring;

    std::string 手持str;
    
    long HeroID;
    bool bFinishGame;
    
    bool shifourenji;
    
    std::string 距离str;
    std::string 名字str;
    
    float HelmetHealth ;
    float ArmorHealth ;
    
    int 头盔护甲等级;
    int 护甲等级;
    
    std::string 头甲str;
    std::string 血量str;

} PlayerInfo;


typedef struct ShareStruct{
    bool gameStatus; // 游戏状态 true:运行中 false:未运行
    pid_t pid;
    uint64_t baseAddress;
    uint64_t readbaseAddress;
    bool antiOk = false;
    
    long Pawn;
    
    MinimalViewInfo MinimalViewInfo;
    Rotation矩阵 Rotation矩阵;
    
    //自己的数据
    PlayerInfo myInfo;
    
    //人物绘制数据
    int actorListcount;
    PlayerInfo playerInfo[100];
    
    
    
} ShareStruct;

typedef struct kfdShareStruct{
    uint64_t ttbr0;
    uint64_t gLibBase;
    uint64_t gLibtersafeBase;
    uint64_t physBase;
    uint64_t physSize;
    uint64_t PPLRW_USER_MAPPING_OFFSET;
    pid_t huizhipid;
    bool ismapped;
    
} kfdShareStruct;

extern ShareStruct *shareData;
extern kfdShareStruct *kfdshareData;

pid_t pid_for_name(const char* name);

#endif /* MemoryShare_hpp */
