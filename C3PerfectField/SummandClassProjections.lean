module

public import C3PerfectField.ScalarExtensionEndQuotients
public import C3PerfectField.FiniteDecomposition

/-!
Projections onto selected indecomposable isomorphism classes.
Their classes modulo the Jacobson radical do not depend on the chosen
indecomposable decomposition. This is the canonical-projection part of
manuscript `lem:end-quotient`, needed for the Galois orbit argument.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat BigOperators Classical

universe u v

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]
  (M : FiniteModule k A) {n : ℕ} (P : Fin n → IndecomposableModule k A)
  (e : M.val ≅ ⨁ fun i => (P i).obj) (S : Set (ARVertex k A))

/-- Projection onto exactly those components whose isomorphism class is in S. -/
def summandClassProjectionHom : M.val ⟶ M.val := by
  classical
  exact e.hom ≫ (∑ i ∈ Finset.univ.filter (fun i => Quotient.mk _ (P i) ∈ S),
    biproduct.π (fun j => (P j).obj) i ≫
      biproduct.ι (fun j => (P j).obj) i) ≫ e.inv

/-- The projection acts as identity or zero on each component inclusion. -/
theorem summandClassProjectionHom_inclusion (i : Fin n) :
    (biproduct.ι (fun j => (P j).obj) i ≫ e.inv) ≫
        summandClassProjectionHom M P e S =
      if Quotient.mk _ (P i) ∈ S then
        biproduct.ι (fun j => (P j).obj) i ≫ e.inv else 0 := by
  classical
  simp [summandClassProjectionHom, Category.assoc, Preadditive.comp_sum,
    Preadditive.sum_comp, biproduct.ι_π_assoc, dite_comp]

/-- The dual component-projection formula. -/
theorem summandClassProjectionHom_projection (i : Fin n) :
    summandClassProjectionHom M P e S ≫
        (e.hom ≫ biproduct.π (fun j => (P j).obj) i) =
      if Quotient.mk _ (P i) ∈ S then
        e.hom ≫ biproduct.π (fun j => (P j).obj) i else 0 := by
  classical
  simp [summandClassProjectionHom, Category.assoc, Preadditive.sum_comp,
    Preadditive.comp_sum, biproduct.ι_π, comp_dite]

/-- The class-selected endomorphism is an actual idempotent before quotienting. -/
theorem summandClassProjectionHom_idempotent :
    summandClassProjectionHom M P e S ≫ summandClassProjectionHom M P e S =
      summandClassProjectionHom M P e S := by
  classical
  apply (cancel_epi e.inv).mp
  apply biproduct.hom_ext'
  intro i
  simp only [← Category.assoc, summandClassProjectionHom_inclusion]
  split_ifs with h
  · exact (summandClassProjectionHom_inclusion M P e S i).trans (ite_eq_left h)
  · simp

/-- Compare arbitrary indecomposable decompositions of the same finite module.
Selection uses actual isomorphism classes, so the difference is radical. -/
theorem isRadical_summandClassProjectionHom_sub
    {m : ℕ} (Q : Fin m → IndecomposableModule k A)
    (d : M.val ≅ ⨁ fun i => (Q i).obj) :
    IsRadical A
      (summandClassProjectionHom M P e S - summandClassProjectionHom M Q d S) := by
  classical
  apply (isRadical_iso_iff e.symm d _).mp
  apply (isRadical_iff_blocks _ _ _).mpr
  intro i j
  let a := biproduct.ι (fun r => (P r).obj) i ≫ e.inv
  let b := d.hom ≫ biproduct.π (fun r => (Q r).obj) j
  change IsRadical A (a ≫
    (summandClassProjectionHom M P e S - summandClassProjectionHom M Q d S) ≫ b)
  have hp : a ≫ summandClassProjectionHom M P e S =
      if Quotient.mk _ (P i) ∈ S then a else 0 :=
    summandClassProjectionHom_inclusion M P e S i
  have hq : summandClassProjectionHom M Q d S ≫ b =
      if Quotient.mk _ (Q j) ∈ S then b else 0 :=
    summandClassProjectionHom_projection M Q d S j
  have hr (h : (Quotient.mk _ (P i) ∈ S) ≠ (Quotient.mk _ (Q j) ∈ S)) :
      IsRadical A (a ≫ b) := by
    apply (isRadical_iff_not_isIso (X := P i) (Y := Q j) _).mpr
    intro hi
    let := hi
    exact h (congrArg (· ∈ S) (Quotient.sound ⟨asIso (a ≫ b)⟩))
  rw [Preadditive.sub_comp, Preadditive.comp_sub,
    ← Category.assoc a (summandClassProjectionHom M P e S) b, hp, hq]
  by_cases hP : Quotient.mk _ (P i) ∈ S
  <;> by_cases hQ : Quotient.mk _ (Q j) ∈ S
  · simp only [hP, hQ, ite_true, sub_self]
    exact isRadical_zero
  · simpa [hP, hQ] using hr (by simp [hP, hQ])
  · have hn : IsRadical A (-(a ≫ b)) :=
      (radicalSubmodule (k := k) (P i).obj (Q j).obj).neg_mem
        (hr (by simp [hP, hQ]))
    simpa [hP, hQ] using hn
  · simp only [hP, hQ, ite_false, zero_comp, comp_zero, sub_self]
    exact isRadical_zero

/-- The canonical quotient class of the selected projection. -/
def summandClassProjection :
    End M.val ⧸ Ideal.jacobson (⊥ : Ideal (End M.val)) :=
  Ideal.Quotient.mk _ (End.of (summandClassProjectionHom M P e S))

theorem summandClassProjection_idempotent :
    IsIdempotentElem (summandClassProjection M P e S) := by
  have h : IsIdempotentElem (End.of (summandClassProjectionHom M P e S)) := by
    apply End.homEquiv.injective
    exact summandClassProjectionHom_idempotent M P e S
  simpa only [summandClassProjection, IsIdempotentElem, map_mul] using
    congrArg (Ideal.Quotient.mk (Ideal.jacobson (⊥ : Ideal (End M.val)))) h

/-- Equality of the quotient classes, with no uniqueness-of-multiplicities
or chosen matrix-algebra isomorphism supplied as a hypothesis. -/
theorem summandClassProjection_eq_of_decomposition
    {m : ℕ} (Q : Fin m → IndecomposableModule k A)
    (d : M.val ≅ ⨁ fun i => (Q i).obj) :
    summandClassProjection M P e S = summandClassProjection M Q d S := by
  apply Ideal.Quotient.eq.mpr
  apply (isRadical_end_iff_mem_jacobson _).mp
  exact isRadical_summandClassProjectionHom_sub M P e S Q d

/-- Any selected nonzero indecomposable component makes the quotient
projection nonzero. -/
theorem summandClassProjection_ne_zero_of_mem (i : Fin n)
    (hi : Quotient.mk _ (P i) ∈ S) :
    summandClassProjection M P e S ≠ 0 := by
  intro hz
  have hr : IsRadical A (summandClassProjectionHom M P e S) :=
    (isRadical_end_iff_mem_jacobson _).mpr (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have h := (hr.precomp (biproduct.ι (fun j => (P j).obj) i ≫ e.inv)).postcomp
    (e.hom ≫ biproduct.π (fun j => (P j).obj) i)
  have he :
      (biproduct.ι (fun j => (P j).obj) i ≫ e.inv) ≫
        summandClassProjectionHom M P e S ≫
          (e.hom ≫ biproduct.π (fun j => (P j).obj) i) = 𝟙 (P i).obj := by
    rw [← Category.assoc, summandClassProjectionHom_inclusion, ite_eq_left hi]
    simp
  exact (P i).property.1 (isRadical_id_iff_isZero.mp (he ▸ h))

/-- An unselected nonzero component prevents the projection from being
the identity, also after quotienting by the Jacobson radical. -/
theorem summandClassProjection_ne_one_of_notMem (i : Fin n)
    (hi : Quotient.mk _ (P i) ∉ S) :
    summandClassProjection M P e S ≠ 1 := by
  intro hz
  have hr : IsRadical A (summandClassProjectionHom M P e S - 𝟙 M.val) :=
    (isRadical_end_iff_mem_jacobson _).mpr (Ideal.Quotient.eq.mp hz)
  have h := (hr.precomp (biproduct.ι (fun j => (P j).obj) i ≫ e.inv)).postcomp
    (e.hom ≫ biproduct.π (fun j => (P j).obj) i)
  have he :
      (biproduct.ι (fun j => (P j).obj) i ≫ e.inv) ≫
        (summandClassProjectionHom M P e S - 𝟙 M.val) ≫
          (e.hom ≫ biproduct.π (fun j => (P j).obj) i) = -𝟙 (P i).obj := by
    rw [Preadditive.sub_comp, Preadditive.comp_sub,
      ← Category.assoc _ (summandClassProjectionHom M P e S),
      summandClassProjectionHom_inclusion, ite_eq_right hi]
    simp
  have hn : IsRadical A (-𝟙 (P i).obj) := he ▸ h
  have hid : IsRadical A (𝟙 (P i).obj) := by
    have hnn : IsRadical A (-(-𝟙 (P i).obj)) :=
      (radicalSubmodule (k := k) (P i).obj (P i).obj).neg_mem hn
    simpa only [neg_neg] using hnn
  exact (P i).property.1 (isRadical_id_iff_isZero.mp hid)

end

end C3PerfectField
