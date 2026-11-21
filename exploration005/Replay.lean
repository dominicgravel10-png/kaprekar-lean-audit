import Lean.Replay
open Lean
def main : IO Unit := do
  initSearchPath (← findSysroot)
  let (mod, _) ← readModuleData "K.olean"
  let env ← importModules mod.imports {} 0
  let constants := mod.constants.foldl (fun acc c => acc.insert c.name c) ({} : Std.HashMap Name ConstantInfo)
  let checked ← Environment.replay constants env
  for name in [`Kaprekar.certified, `Kaprekar.E, `Kaprekar.sortedMultiplicity] do
    unless checked.contains name do throw (IO.userError s!"Missing {name}")
  IO.println s!"Kernel replay OK ({constants.size} module constants supplied)"
