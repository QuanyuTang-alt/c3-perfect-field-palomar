module

public import C3PerfectField.AlmostSplitExistence
public import C3PerfectField.ProjectiveAlmostSplit
public import C3PerfectField.DualIndecomposables
public import C3PerfectField.AlmostSplitSuccessors
public import C3PerfectField.WeightedGraph

/-!
Manuscript Proposition `prop:local`, for the actual AR quiver.
Almost split existence and the transpose estimate handle nonprojectives;
the radical inclusion handles projectives. Field duality gives successors.
The resulting weighted graph uses exactly the module-isomorphism classes,
arrows and dimension weights in the target statement.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

open CategoryTheory
open scoped ModuleCat BigOperators

universe u v

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]
  [FiniteDimensional k A]

theorem exists_rightAlmostSplit_source_bound (X : IndecomposableModule k A) :
    ∃ (E : FiniteModule k A) (q : E.val ⟶ X.obj),
      IsRightAlmostSplit (k := k) q ∧
        Module.finrank k E.val ≤
          (1 + (Module.finrank k A) ^ 2) * Module.finrank k X.obj := by
  classical
  by_cases hX : Projective X.obj
  · refine ⟨finiteSubmoduleModule X.val (Module.jacobson A X.obj),
      submoduleInclusion X.val (Module.jacobson A X.obj),
      isRightAlmostSplit_jacobsonInclusion_projective X hX, ?_⟩
    exact (finrank_submoduleModule_le X.val (Module.jacobson A X.obj)).trans
      (by
        calc
          Module.finrank k X.obj = 1 * Module.finrank k X.obj := (Nat.one_mul _).symm
          _ ≤ (1 + (Module.finrank k A) ^ 2) * Module.finrank k X.obj :=
            Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
  · exact exists_rightAlmostSplit_source_bound_nonprojective X hX

theorem finite_arPredecessors (x : ARVertex k A) :
    Set.Finite {y : ARVertex k A | ARArrow k A y x} := by
  induction x using Quotient.inductionOn with
  | h X =>
    obtain ⟨E, q, hq, _⟩ := exists_rightAlmostSplit_source_bound X
    exact finite_arPredecessors_of_rightAlmostSplit q hq

theorem arPredecessor_sum_le_uniform_bound (X : IndecomposableModule k A) :
    ∑ y ∈ (finite_arPredecessors (Quotient.mk _ X : ARVertex k A)).toFinset,
      arDimension y ≤ (1 + (Module.finrank k A) ^ 2) * Module.finrank k X.obj := by
  obtain ⟨E, q, hq, hE⟩ := exists_rightAlmostSplit_source_bound X
  apply (sum_arDimension_predecessors_le_of_rightAlmostSplit q hq _ ?_).trans hE
  intro y hy
  exact (finite_arPredecessors (Quotient.mk _ X : ARVertex k A)).mem_toFinset.mp hy

theorem exists_leftAlmostSplit_target_bound (X : IndecomposableModule k A) :
    ∃ (E : FiniteModule k A) (p : X.obj ⟶ E.val),
      IsLeftAlmostSplit (k := k) p ∧
        Module.finrank k E.val ≤
          (1 + (Module.finrank k A) ^ 2) * Module.finrank k X.obj := by
  obtain ⟨E, q, hq, hE⟩ :=
    exists_rightAlmostSplit_source_bound (leftDualIndecomposable X)
  refine ⟨finiteRightDualModule E, dualizedRightAlmostSplitMap q,
    isLeftAlmostSplit_dualizedRightAlmostSplitMap q hq, ?_⟩
  have hop : Module.finrank k Aᵐᵒᵖ = Module.finrank k A :=
    (MulOpposite.opLinearEquiv k (M := A)).symm.finrank_eq
  change Module.finrank k E.val ≤
    (1 + (Module.finrank k Aᵐᵒᵖ) ^ 2) *
      Module.finrank k (leftDualModule (k := k) X.obj) at hE
  rw [hop, finrank_leftDualModule X.val] at hE
  change Module.finrank k (rightDualModule (k := k) E.val) ≤ _
  rw [finrank_rightDualModule E]
  exact hE

theorem finite_arSuccessors (x : ARVertex k A) :
    Set.Finite {y : ARVertex k A | ARArrow k A x y} := by
  induction x using Quotient.inductionOn with
  | h X =>
    obtain ⟨E, p, hp, _⟩ := exists_leftAlmostSplit_target_bound X
    exact finite_arSuccessors_of_leftAlmostSplit p hp

theorem arSuccessor_sum_le_uniform_bound (X : IndecomposableModule k A) :
    ∑ y ∈ (finite_arSuccessors (Quotient.mk _ X : ARVertex k A)).toFinset,
      arDimension y ≤ (1 + (Module.finrank k A) ^ 2) * Module.finrank k X.obj := by
  obtain ⟨E, p, hp, hE⟩ := exists_leftAlmostSplit_target_bound X
  apply (sum_arDimension_successors_le_of_leftAlmostSplit p hp _ ?_).trans hE
  intro y hy
  exact (finite_arSuccessors (Quotient.mk _ X : ARVertex k A)).mem_toFinset.mp hy

/-- The actual AR quiver satisfies every field of the weighted graph
structure used by the verified period argument, without added premises. -/
noncomputable def arWeightedDigraph : WeightedDigraph (ARVertex k A) where
  arrow := ARArrow k A
  predecessors := fun x => (finite_arPredecessors x).toFinset
  successors := fun x => (finite_arSuccessors x).toFinset
  mem_predecessors := fun x y => (finite_arPredecessors y).mem_toFinset
  mem_successors := fun x y => (finite_arSuccessors x).mem_toFinset
  weight := arDimension
  weight_pos := arDimension_pos
  bound := 1 + (Module.finrank k A) ^ 2
  bound_pos := by omega
  predecessor_bound := by
    intro x
    induction x using Quotient.inductionOn with
    | h X =>
      simpa only [arDimension_mk] using arPredecessor_sum_le_uniform_bound X
  successor_bound := by
    intro x
    induction x using Quotient.inductionOn with
    | h X =>
      simpa only [arDimension_mk] using arSuccessor_sum_le_uniform_bound X

theorem arWeightedDigraph_underlyingGraph :
    (arWeightedDigraph (k := k) (A := A)).underlyingGraph = ARGraph k A := rfl

end C3PerfectField
