import LeanChecker

/- Lean 4.36 caches module-root names across replays. Resolve each root using a
   name owned by the process before leanchecker frees its first imported
   environment. Running this file with `lean --run` then invokes the imported
   LeanChecker.main with its ordinary arguments and kernel checks. -/
open Lean in
#eval do
  initSearchPath (← findSysroot)
  for dir in ← searchPathRef.get do
    if ← dir.isDir then
      for entry in ← dir.readDir do
        if ← entry.path.isDir then
          discard <| findOLean (.mkSimple entry.fileName)
        else if entry.path.extension == some "olean" then
          if let some stem := entry.path.fileStem then
            discard <| findOLean (.mkSimple stem)
