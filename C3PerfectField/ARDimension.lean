module

public import C3PerfectField.FiniteDecomposition
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
The dimension weight on the actual Auslander--Reiten vertices.
Counting each isomorphism class once gives a sum bounded by the dimension
of any module containing those classes as indecomposable summands.
No uniqueness of decomposition multiplicities is needed for this estimate.
-/

@[expose] public section

namespace C3PerfectField

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat BigOperators

universe u v

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

/-- Vector-space dimension is unchanged by an `A`-module isomorphism. -/
theorem finrank_eq_of_module_iso {X Y : ModuleCat.{max u v} A} (e : X ≅ Y) :
    Module.finrank k X = Module.finrank k Y :=
  (e.toLinearEquiv.restrictScalars k).finrank_eq

/-- The positive dimension weight from manuscript `prop:local`, defined
on actual indecomposable isomorphism classes. -/
noncomputable def arDimension : ARVertex k A → ℕ :=
  Quotient.lift (fun X : IndecomposableModule k A => Module.finrank k X.obj)
    (fun _ _ ⟨e⟩ => finrank_eq_of_module_iso e)

@[simp]
theorem arDimension_mk (X : IndecomposableModule k A) :
    arDimension (Quotient.mk _ X : ARVertex k A) = Module.finrank k X.obj := rfl

theorem arDimension_pos (x : ARVertex k A) : 0 < arDimension x := by
  obtain ⟨X, rfl⟩ := Quotient.exists_rep x
  rw [arDimension_mk]
  let : Module.Finite k X.obj := X.val.property
  let : Nontrivial X.obj := not_subsingleton_iff_nontrivial.mp
    (fun hs => X.property.1 (ModuleCat.isZero_iff_subsingleton.mpr hs))
  exact Module.finrank_pos

/-- Every finite set of distinct indecomposable summand classes has
total dimension at most that of the ambient module. Repeated isomorphic
components of a chosen decomposition are counted only once on the left. -/
theorem sum_arDimension_le_finrank_of_summands
    (W : FiniteModule k A) (s : Finset (ARVertex k A))
    (hs : ∀ x ∈ s, ∃ X : IndecomposableModule k A,
      Quotient.mk _ X = x ∧ IsIndecomposableSummand X W) :
    ∑ x ∈ s, arDimension x ≤ Module.finrank k W.val := by
  classical
  obtain ⟨n, P, ⟨e⟩⟩ := exists_indecomposable_biproduct W
  let f : Fin n → ARVertex k A := fun i => Quotient.mk _ (P i)
  have hsub : s ⊆ Finset.univ.image f := by
    intro x hx
    obtain ⟨X, rfl, hX⟩ := hs x hx
    obtain ⟨i, hi⟩ := (isIndecomposableSummand_iff_component_iso X W P e).mp hX
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, (Quotient.sound hi).symm⟩
  calc
    ∑ x ∈ s, arDimension x ≤ ∑ x ∈ Finset.univ.image f, arDimension x :=
      Finset.sum_le_sum_of_subset hsub
    _ ≤ ∑ i : Fin n, arDimension (f i) :=
      Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)
    _ = Module.finrank k W.val := by
      simpa only [f, arDimension_mk] using
        (finrank_eq_sum_of_indecomposable_biproduct W P e).symm

end C3PerfectField
