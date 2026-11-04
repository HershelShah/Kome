/-
The axiom check (AUDIT A18).

`lake build` compiles this file, so the build fails when a declaration of
`Kome.Frontier` uses an axiom outside the standard three (`propext`,
`Classical.choice` and `Quot.sound`). A `sorry` adds the axiom `sorryAx`,
so it fails this check. (`build.sh` also runs `lake build --wfail`, so the
`sorry` warning itself fails the build.)

The command `#assert_std_axioms M` checks every declaration of the module
`M`: each theorem that the README lists, every lemma under it, and every
definition. It does not check a list of names, so a theorem that is added
later is checked without a change here.
-/
import Lean
import Kome.Frontier

namespace Kome.Axioms

open Lean Elab Command

/-- The axioms that a proof may use. -/
def allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- `#assert_std_axioms M`: every declaration of the imported module `M` uses
only the axioms in `allowed`. Otherwise the command is an error, and the
message names each offending declaration and axiom. -/
elab "#assert_std_axioms " m:ident : command => do
  let env ← getEnv
  let mod := m.getId
  let some idx := env.getModuleIdx? mod
    | throwErrorAt m "module {mod} is not imported"
  let names := env.header.moduleData[idx.toNat]!.constNames
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  let mut bad : Array (Name × Name) := #[]
  for n in names do
    checked := checked + 1
    if let some (.thmInfo _) := env.find? n then
      theorems := theorems + 1
    let axioms ← collectAxioms n
    for ax in axioms do
      unless allowed.contains ax do
        bad := bad.push (n, ax)
  unless bad.isEmpty do
    let lines := bad.map fun (n, ax) => m!"  {n} uses {ax}"
    throwErrorAt m "{mod}: {bad.size} declaration(s) use an axiom outside {allowed}:\n{MessageData.joinSep lines.toList "\n"}"
  logInfo m!"{mod}: {checked} declarations ({theorems} theorem constants) use only the axioms {allowed}"

end Kome.Axioms

#assert_std_axioms Kome.Frontier
