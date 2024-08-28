// rootProject.name = "Tai-e" // Mismatch between project name and folder name may cause Intellij error

include(
    ":", // root project
    "docs",
    "jasmine1"
)
project(":jasmine1").projectDir = file("jasmine1")
