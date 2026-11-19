import Lake
open Lake DSL System

package vsync

@[default_target]
lean_lib VSync

@[default_target]
lean_exe vsync where
  root := `Main

/-- Tiny C helper for atomic, durable file writes (native/vsync_io.c). -/
target vsync_io.o pkg : FilePath := do
  let oFile := pkg.buildDir / "native" / "vsync_io.o"
  let srcJob ← inputTextFile <| pkg.dir / "native" / "vsync_io.c"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC", "-O2"] "cc" getLeanTrace

extern_lib vsyncio pkg := do
  let o ← vsync_io.o.fetch
  let name := nameToStaticLib "vsyncio"
  buildStaticLib (pkg.staticLibDir / name) #[o]
