module

public import C3PerfectField.ARDimension

/-!
The predecessor-summand argument from manuscript `lem:predecessor-summand`.
Existence and dimension estimates for right almost split maps remain
separate obligations: no such map is assumed by the main statement.
-/

@[expose] public section

namespace C3PerfectField

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat BigOperators

universe u v

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

/-- Manuscript Definition `def:modules`, in the finite-dimensional category:
every nonretraction into the target factors through this nonretraction. -/
def IsRightAlmostSplit {E X : FiniteModule k A} (q : E.val ⟶ X.val) : Prop :=
  ¬IsSplitEpi q ∧ ∀ (Y : FiniteModule k A) (f : Y.val ⟶ X.val),
    ¬IsSplitEpi f → ∃ a : Y.val ⟶ E.val, f = a ≫ q

/-- Manuscript `lem:predecessor-summand`, for the actual factorization
definition of irreducibility. -/
theorem isIndecomposableSummand_of_irreducible_rightAlmostSplit
    {X Y : IndecomposableModule k A} {E : FiniteModule k A}
    (q : E.val ⟶ X.obj) (hq : IsRightAlmostSplit (k := k) q)
    (f : Y.obj ⟶ X.obj) (hf : IsIrreducibleMorphism (k := k) f) :
    IsIndecomposableSummand Y E := by
  obtain ⟨a, hfac⟩ := hq.2 Y.val f hf.2.1
  have hs : IsSplitMono a := (hf.2.2 E a q hfac).resolve_right hq.1
  let := hs
  exact ⟨a, retraction a, IsSplitMono.id a⟩

/-- Every actual arrow into the target of a right almost split map comes
from a summand of its source, using the proved radical/irreducibility bridge. -/
theorem isIndecomposableSummand_of_arrow_rightAlmostSplit
    {X Y : IndecomposableModule k A} {E : FiniteModule k A}
    (q : E.val ⟶ X.obj) (hq : IsRightAlmostSplit (k := k) q)
    (h : HasARArrow k A Y X) : IsIndecomposableSummand Y E := by
  obtain ⟨f, hf⟩ := hasARArrow_iff_exists_irreducible.mp h
  exact isIndecomposableSummand_of_irreducible_rightAlmostSplit q hq f hf

/-- An arrow predecessor matches a component of any decomposition of the
source of a right almost split map. -/
theorem predecessor_iso_component_of_rightAlmostSplit
    {X Y : IndecomposableModule k A} {E : FiniteModule k A}
    (q : E.val ⟶ X.obj) (hq : IsRightAlmostSplit (k := k) q)
    {n : ℕ} (P : Fin n → IndecomposableModule k A)
    (e : E.val ≅ ⨁ fun i => (P i).obj) (h : HasARArrow k A Y X) :
    ∃ i, Nonempty (Y.obj ≅ (P i).obj) :=
  (isIndecomposableSummand_iff_component_iso Y E P e).mp
    (isIndecomposableSummand_of_arrow_rightAlmostSplit q hq h)

/-- For such a map, the actual AR predecessors on isomorphism classes form
a finite set. This proves the finiteness step independently of the still
unproved global existence theorem for almost split maps. -/
theorem finite_arPredecessors_of_rightAlmostSplit
    {X : IndecomposableModule k A} {E : FiniteModule k A}
    (q : E.val ⟶ X.obj) (hq : IsRightAlmostSplit (k := k) q) :
    Set.Finite {y : ARVertex k A | ARArrow k A y (Quotient.mk _ X)} := by
  classical
  obtain ⟨n, P, ⟨e⟩⟩ := exists_indecomposable_biproduct E
  have hr : Set.Finite (Set.range fun i : Fin n =>
      (Quotient.mk _ (P i) : ARVertex k A)) := Set.finite_range _
  apply hr.subset
  intro y hy
  obtain ⟨Y, rfl⟩ := Quotient.exists_rep y
  have h : HasARArrow k A Y X := (arArrow_mk_iff Y X).mp hy
  obtain ⟨i, hi⟩ := predecessor_iso_component_of_rightAlmostSplit q hq P e h
  exact ⟨i, (Quotient.sound hi).symm⟩

/-- The weighted predecessor estimate for a given right almost split map.
Each isomorphism class in `s` is counted once. -/
theorem sum_arDimension_predecessors_le_of_rightAlmostSplit
    {X : IndecomposableModule k A} {E : FiniteModule k A}
    (q : E.val ⟶ X.obj) (hq : IsRightAlmostSplit (k := k) q)
    (s : Finset (ARVertex k A))
    (hs : ∀ y ∈ s, ARArrow k A y (Quotient.mk _ X)) :
    ∑ y ∈ s, arDimension y ≤ Module.finrank k E.val := by
  apply sum_arDimension_le_finrank_of_summands E s
  intro y hy
  obtain ⟨Y, rfl⟩ := Quotient.exists_rep y
  exact ⟨Y, rfl, isIndecomposableSummand_of_arrow_rightAlmostSplit q hq
    ((arArrow_mk_iff Y X).mp (hs _ hy))⟩

/-- Summing over the entire actual predecessor set gives the same estimate.
Finiteness is proved from `q`, rather than supplied as a separate premise. -/
theorem arPredecessor_sum_le_source_dimension
    {X : IndecomposableModule k A} {E : FiniteModule k A}
    (q : E.val ⟶ X.obj) (hq : IsRightAlmostSplit (k := k) q) :
    ∑ y ∈ (finite_arPredecessors_of_rightAlmostSplit q hq).toFinset,
      arDimension y ≤ Module.finrank k E.val := by
  apply sum_arDimension_predecessors_le_of_rightAlmostSplit q hq
  intro y hy
  exact (finite_arPredecessors_of_rightAlmostSplit q hq).mem_toFinset.mp hy

/-- The numerical reduction in manuscript `prop:local`: a dimension bound
on the source implies the weighted predecessor bound. Existence of such
maps and their uniform source estimate remain separate obligations. -/
theorem arPredecessor_sum_le_of_source_bound
    {X : IndecomposableModule k A} {E : FiniteModule k A}
    (q : E.val ⟶ X.obj) (hq : IsRightAlmostSplit (k := k) q)
    (C : ℕ) (hE : Module.finrank k E.val ≤ C * Module.finrank k X.obj) :
    ∑ y ∈ (finite_arPredecessors_of_rightAlmostSplit q hq).toFinset,
      arDimension y ≤ C * arDimension (Quotient.mk _ X : ARVertex k A) := by
  simpa only [arDimension_mk] using
    (arPredecessor_sum_le_source_dimension q hq).trans hE

end C3PerfectField
