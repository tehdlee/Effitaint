plugins {
    id("java")
}

group = "org.jasmine"
version = "1.0-SNAPSHOT"

repositories {
    jcenter()
    mavenCentral()
    maven {
        url = uri("https://repo1.maven.org/maven2/")
    }
    maven {
        url = uri("https://soot-build.cs.uni-paderborn.de/nexus/repository/soot-snapshot/")
    }
    maven {
        url = uri("https://soot-build.cs.uni-paderborn.de/nexus/repository/soot-release/")
    }
}

dependencies {
    implementation("org.soot-oss:soot:4.2.0")
    implementation("org.slf4j:slf4j-nop:1.7.5")
    implementation("org.graphstream:gs-core:1.3")
    implementation("org.graphstream:gs-ui:1.3")
    implementation("log4j:log4j:1.2.15") {
        exclude(group = "javax.jms", module = "jms")
        exclude(group = "com.sun.jdmk", module = "jmxtools")
        exclude(group = "com.sun.jmx", module = "jmxri")
    }
    implementation("junit:junit:4.12")
    implementation("org.dom4j:dom4j:2.0.3")
    implementation("com.alibaba:fastjson:1.2.73")
    // implementation(fileTree(mapOf("dir" to "libs", "include" to listOf("*.jar"))))
    implementation("org.aspectj:aspectjweaver:1.9.6")
    // https://mvnrepository.com/artifact/org.springframework/spring-webmvc
    implementation("org.springframework:spring-webmvc:5.2.12.RELEASE")
}
