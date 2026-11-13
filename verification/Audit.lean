module

import all C3Integration
import all Solution
import Lean.Util.CollectAxioms

/-! Mechanical regression checks of the advertised declarations. -/
open scoped ModuleCat
universe u
example (k A : Type u) [Field k] [Ring A] [Algebra k A]
    [PerfectField k] [FiniteDimensional k A]
    (hA : C3PerfectField.InfiniteRepresentationType k A) :
    Infinite (C3PerfectField.ARGraph k A).ConnectedComponent :=
  PalomarC3.main_result k A hA

run_cmd do
  for name in #[``C3PerfectField.indecomposable_iff_largeIndecomposable,
      ``C3PerfectField.not_representationFinite_of_infiniteRepresentationType,
      ``C3PerfectField.infinite_arComponents_algebraicallyClosed,
      ``C3PerfectField.mainTheorem, ``PalomarC3.main_result] do
    let env ← Lean.getEnv
    unless (env.find? name).any (fun i => match i with | .thmInfo _ => true | _ => false) do
      throwError "Not a theorem: {name}"
    let axioms ← Lean.collectAxioms name
    let forbidden := axioms.filter fun a =>
      !#[``propext, ``Classical.choice, ``Quot.sound].contains a
    unless forbidden.isEmpty do
      throwError "Forbidden axioms for {name}: {forbidden}"
    Lean.logInfo m!"{name}: {axioms}"
#print C3PerfectField.mainTheorem
#print PalomarC3.main_result
