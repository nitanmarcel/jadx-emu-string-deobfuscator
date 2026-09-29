# string-deobfuscator

[jadx-emu](https://github.com/nitanmarcel/jadx-emu) extension for decrypting strings using emulation.

Before:

```java
String a = dec(new byte[]{123, 82, 46, 27, 124}, 0);
String c = (String) dispatch(0);
String d = POOL[1] + "/" + POOL[2];
String e = new String(rawBytes());
```

After:

```java
String a = "hello";
String c = "cast-me";
String d = "secret/device-id";
String e = "hello";
```

## Build

```sh
./gradlew jar
```
