import Lake

open Lake DSL

/-- Linger's own build, which linger requires first so that it comes first on linger's search
path, ahead of its packages' builds: each package names its challenge `Challenge`, as linger
does. It declares nothing. -/
package first where buildDir := "../.lake/build"
