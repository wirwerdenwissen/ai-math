import Lean
open Lean

/-!
The kernel guarantee: nothing under `Results/` may depend on `sorry`,
`native_decide`, or any axiom beyond Lean's three. It asks the environment what
each declaration actually depends on, so nothing hides behind a tactic, a
definition or an import.

It finds the results by reading the directory, so there is no index to keep up
to date: add a file and it is checked.

Run: `lake env lean --run scripts/CheckAxioms.lean`
-/

def allowedAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Every module under `Results/`, found by walking the directory. -/
def resultModules : IO (Array Name) := do
  let dir : System.FilePath := "Results"
  unless ← dir.pathExists do return #[]
  let paths ← dir.walkDir
  let mut modules := #[]
  for path in paths do
    if path.extension == some "lean" then
      if let some stem := path.fileStem then
        let dirs := (path.parent.map (·.components)).getD []
        let parts := dirs ++ [stem]
        modules := modules.push (List.foldl Name.mkStr Name.anonymous parts)
  return modules.qsort (·.toString < ·.toString)

/-- `collectAxioms` needs only a monad that can hand it the environment. -/
abbrev CheckM := ReaderT Environment IO

instance : MonadEnv CheckM where
  getEnv := read
  modifyEnv _ := pure ()

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let modules ← resultModules
  if modules.isEmpty then
    IO.println "No results yet."
    return 0
  let env ← importModules (modules.map ({ module := · })) {}
  let mut bad : Nat := 0
  let mut checked : Nat := 0
  for (name, _) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`Results).isPrefixOf mod do continue
    checked := checked + 1
    let axioms ← (collectAxioms name : CheckM (Array Name)).run env
    let extra := axioms.filter (!allowedAxioms.contains ·)
    unless extra.isEmpty do
      IO.eprintln s!"REJECT {mod} :: {name} depends on {extra}"
      bad := bad + 1
  IO.println s!"Checked {checked} declarations in {modules.size} \
    module(s), {bad} rejected."
  return if bad == 0 then 0 else 1
