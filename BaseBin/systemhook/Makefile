TARGET = systemhook.dylib
CC = clang

CFLAGS = -framework Foundation -framework UIKit -framework CoreServices -framework Security -I../.include -I./src -I../_external/modules/litehook/src -isysroot $(shell xcrun --sdk iphoneos --show-sdk-path) -arch arm64 -arch arm64e -miphoneos-version-min=15.0 -install_name $(TARGET) -Wno-deprecated-declarations -Os -moutline
LDFLAGS = -dynamiclib -ldobby

sign: $(TARGET)
	@ldid -S $^

$(TARGET): $(wildcard src/*.c src/*.m src/*.o ../libjailbreak/src/jbclient_*.c ../_external/modules/litehook/src/*.c ../libjailbreak/src/roothider/jailbreakd.c)
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $^

clean:
	@rm -f $(TARGET)
