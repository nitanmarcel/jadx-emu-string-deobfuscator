import org.jetbrains.kotlin.gradle.dsl.JvmTarget

plugins {
    kotlin("jvm") version "2.3.10"
}

version = System.getenv("VERSION") ?: "dev"

repositories {
    mavenLocal()
    mavenCentral()
    google()
}

dependencies {
    compileOnly("io.github.nitanmarcel:jadx-emu:0.1.0-beta.4")

    compileOnly("io.github.skylot:jadx-core:1.5.6")
    compileOnly(kotlin("stdlib"))
    compileOnly("org.slf4j:slf4j-api:2.0.17")
}

java {
    toolchain {
        languageVersion = JavaLanguageVersion.of(21)
    }
}

kotlin {
    compilerOptions {
        jvmTarget = JvmTarget.JVM_21
    }
}

tasks.jar {
    archiveBaseName = "string-deobfuscator"
}
