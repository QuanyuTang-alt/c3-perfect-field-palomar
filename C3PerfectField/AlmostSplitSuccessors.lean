module

public import C3PerfectField.DualMorphisms
public import C3PerfectField.AlmostSplitPredecessors

/-!
The successor counterpart of the predecessor-summand argument. Field duality
turns a given right almost split map into a left almost split map and
preserves the dimension needed for the successor sum.
Existence of right almost split maps remains a separate obligation.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat BigOperators

universe u v

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

/-- Every nonsection out of the source factors through this nonsection. -/
def IsLeftAlmostSplit {X E : FiniteModule k A} (p : X.val ⟶ E.val) : Prop :=
  ¬IsSplitMono p ∧ ∀ (Y : FiniteModule k A) (f : X.val ⟶ Y.val),
    ¬IsSplitMono f → ∃ b : E.val ⟶ Y.val, f = p ≫ b

/-- Dualize a right almost split map into `D X`, using the actual
double-dual module isomorphism to put its source back at `X`. -/
noncomputable def dualizedRightAlmostSplitMap {X : FiniteModule k A}
    {E : FiniteModule k Aᵐᵒᵖ} (q : E.val ⟶ (finiteLeftDualModule X).val) :
    X.val ⟶ (finiteRightDualModule E).val :=
  (doubleDualModuleIso X).hom ≫ rightDualMap q

theorem isLeftAlmostSplit_dualizedRightAlmostSplitMap {X : FiniteModule k A}
    {E : FiniteModule k Aᵐᵒᵖ} (q : E.val ⟶ (finiteLeftDualModule X).val)
    (hq : IsRightAlmostSplit (k := k) q) :
    IsLeftAlmostSplit (k := k) (dualizedRightAlmostSplitMap q) := by
  constructor
  · intro hp
    let := hp
    have hmono : IsSplitMono (rightDualMap (k := k) q) := by
      have heq : (doubleDualModuleIso X).inv ≫ dualizedRightAlmostSplitMap q =
          rightDualMap (k := k) q := by
        simp [dualizedRightAlmostSplitMap]
      rw [← heq]
      infer_instance
    exact hq.1 ((rightDualMap_isSplitMono_iff (M := E) (N := finiteLeftDualModule X) q).mp
      hmono)
  · intro Y f hf
    have hdual : ¬IsSplitEpi (leftDualMap (k := k) f) := by
      intro h
      exact hf ((leftDualMap_isSplitEpi_iff f).mp h)
    obtain ⟨a, ha⟩ := hq.2 (finiteLeftDualModule Y) (leftDualMap f) hdual
    refine ⟨rightDualMap a ≫ (doubleDualModuleIso Y).inv, ?_⟩
    rw [doubleDual_conjugate f, ha, rightDualMap_comp]
    simp only [dualizedRightAlmostSplitMap, Category.assoc]

theorem isIndecomposableSummand_of_irreducible_leftAlmostSplit
    {X Y : IndecomposableModule k A} {E : FiniteModule k A}
    (p : X.obj ⟶ E.val) (hp : IsLeftAlmostSplit (k := k) p)
    (f : X.obj ⟶ Y.obj) (hf : IsIrreducibleMorphism (k := k) f) :
    IsIndecomposableSummand Y E := by
  obtain ⟨b, hfac⟩ := hp.2 Y.val f hf.1
  have hb : IsSplitEpi b := (hf.2.2 E p b hfac).resolve_left hp.1
  let := hb
  exact ⟨section_ b, b, IsSplitEpi.id b⟩

theorem isIndecomposableSummand_of_arrow_leftAlmostSplit
    {X Y : IndecomposableModule k A} {E : FiniteModule k A}
    (p : X.obj ⟶ E.val) (hp : IsLeftAlmostSplit (k := k) p)
    (h : HasARArrow k A X Y) : IsIndecomposableSummand Y E := by
  obtain ⟨f, hf⟩ := hasARArrow_iff_exists_irreducible.mp h
  exact isIndecomposableSummand_of_irreducible_leftAlmostSplit p hp f hf

theorem successor_iso_component_of_leftAlmostSplit
    {X Y : IndecomposableModule k A} {E : FiniteModule k A}
    (p : X.obj ⟶ E.val) (hp : IsLeftAlmostSplit (k := k) p)
    {n : ℕ} (P : Fin n → IndecomposableModule k A)
    (e : E.val ≅ ⨁ fun i => (P i).obj) (h : HasARArrow k A X Y) :
    ∃ i, Nonempty (Y.obj ≅ (P i).obj) :=
  (isIndecomposableSummand_iff_component_iso Y E P e).mp
    (isIndecomposableSummand_of_arrow_leftAlmostSplit p hp h)

theorem finite_arSuccessors_of_leftAlmostSplit
    {X : IndecomposableModule k A} {E : FiniteModule k A}
    (p : X.obj ⟶ E.val) (hp : IsLeftAlmostSplit (k := k) p) :
    Set.Finite {y : ARVertex k A | ARArrow k A (Quotient.mk _ X) y} := by
  classical
  obtain ⟨n, P, ⟨e⟩⟩ := exists_indecomposable_biproduct E
  have hr : Set.Finite (Set.range fun i : Fin n =>
      (Quotient.mk _ (P i) : ARVertex k A)) := Set.finite_range _
  apply hr.subset
  intro y hy
  obtain ⟨Y, rfl⟩ := Quotient.exists_rep y
  have h : HasARArrow k A X Y := (arArrow_mk_iff X Y).mp hy
  obtain ⟨i, hi⟩ := successor_iso_component_of_leftAlmostSplit p hp P e h
  exact ⟨i, (Quotient.sound hi).symm⟩

theorem sum_arDimension_successors_le_of_leftAlmostSplit
    {X : IndecomposableModule k A} {E : FiniteModule k A}
    (p : X.obj ⟶ E.val) (hp : IsLeftAlmostSplit (k := k) p)
    (s : Finset (ARVertex k A))
    (hs : ∀ y ∈ s, ARArrow k A (Quotient.mk _ X) y) :
    ∑ y ∈ s, arDimension y ≤ Module.finrank k E.val := by
  apply sum_arDimension_le_finrank_of_summands E s
  intro y hy
  obtain ⟨Y, rfl⟩ := Quotient.exists_rep y
  exact ⟨Y, rfl, isIndecomposableSummand_of_arrow_leftAlmostSplit p hp
    ((arArrow_mk_iff X Y).mp (hs _ hy))⟩

theorem arSuccessor_sum_le_target_dimension
    {X : IndecomposableModule k A} {E : FiniteModule k A}
    (p : X.obj ⟶ E.val) (hp : IsLeftAlmostSplit (k := k) p) :
    ∑ y ∈ (finite_arSuccessors_of_leftAlmostSplit p hp).toFinset,
      arDimension y ≤ Module.finrank k E.val := by
  apply sum_arDimension_successors_le_of_leftAlmostSplit p hp
  intro y hy
  exact (finite_arSuccessors_of_leftAlmostSplit p hp).mem_toFinset.mp hy

/-- A right almost split map into `D X` gives the full successor sum bound
with its source dimension, since taking the field dual preserves dimension. -/
theorem arSuccessor_sum_le_dual_source_dimension
    {X : IndecomposableModule k A} {E : FiniteModule k Aᵐᵒᵖ}
    (q : E.val ⟶ (finiteLeftDualModule X.val).val)
    (hq : IsRightAlmostSplit (k := k) q) :
    ∑ y ∈ (finite_arSuccessors_of_leftAlmostSplit (dualizedRightAlmostSplitMap q)
      (isLeftAlmostSplit_dualizedRightAlmostSplitMap q hq)).toFinset,
      arDimension y ≤ Module.finrank k E.val := by
  have h := arSuccessor_sum_le_target_dimension (X := X) (dualizedRightAlmostSplitMap q)
    (isLeftAlmostSplit_dualizedRightAlmostSplitMap q hq)
  simpa only [finiteRightDualModule, finrank_rightDualModule] using h

end C3PerfectField
