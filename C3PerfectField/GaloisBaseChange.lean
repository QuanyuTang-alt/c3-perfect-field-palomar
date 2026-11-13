module

public import C3PerfectField.RationalGaloisDegree
public import Mathlib.FieldTheory.SeparableClosure

/-!
The compositum step in manuscript Lemma `lem:cyclic-fg`.
Adjoining a finite Galois subextension to a larger base is Galois;
restriction injects its automorphism group into the original one.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

universe u v

variable {P : Type u} {k : Type v} [Field P] [Field k] [Algebra P k]
  (L : IntermediateField P k) [FiniteDimensional P L] [IsGalois P L]
  (F : Type v) [Field F] [Algebra P F] [Algebra F k] [IsScalarTower P F k]

/-- The same splitting polynomial realizes the compositum over the new base. -/
theorem isGalois_adjoin_of_isGalois :
    IsGalois F (IntermediateField.adjoin F (L : Set k)) := by
  let M := IntermediateField.adjoin F (L : Set k)
  have hsep : Algebra.IsSeparable F M := by
    apply (IntermediateField.isSeparable_adjoin_iff_isSeparable F k).mpr
    intro x hx
    exact ((Algebra.IsSeparable.isSeparable P (⟨x, hx⟩ : L)).map
      L.val L.val.injective).tower_top F
  obtain ⟨p, hp⟩ := Normal.exists_isSplittingField P L
  let := hp
  have hL : L = IntermediateField.adjoin P (p.rootSet k) :=
    (IntermediateField.isSplittingField_iff.mp hp).2
  have hM : M = IntermediateField.adjoin F ((p.map (algebraMap P F)).rootSet k) := by
    simp only [Polynomial.rootSet_map]
    change IntermediateField.adjoin F (L : Set k) = _
    rw [hL, IntermediateField.adjoin_adjoin_right]
  have hsplit : ((p.map (algebraMap P F)).map (algebraMap F k)).Splits := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    have h := (Polynomial.IsSplittingField.splits L p).map L.subtype
    have hr : L.subtype.comp (algebraMap P L) = algebraMap P k :=
      RingHom.ext fun a => IntermediateField.coe_algebraMap_apply L a
    rwa [Polynomial.map_map, hr] at h
  let : (p.map (algebraMap P F)).IsSplittingField F M := hM ▸
    IntermediateField.adjoin_rootSet_isSplittingField hsplit
  exact {
    to_isSeparable := hsep
    to_normal := Normal.of_isSplittingField (p.map (algebraMap P F))
  }

/-- Restriction to the original extension is injective because its image
and the new base generate the whole compositum. -/
theorem finrank_adjoin_dvd_of_isGalois :
    Module.finrank F (IntermediateField.adjoin F (L : Set k)) ∣
      Module.finrank P L := by
  classical
  let M := IntermediateField.adjoin F (L : Set k)
  let := finiteDimensional_adjoin_of_finiteDimensional L F
  let := isGalois_adjoin_of_isGalois L F
  let i : L →ₐ[P] M := IntermediateField.inclusion
    (show L ≤ M.restrictScalars P from IntermediateField.subset_adjoin F (L : Set k))
  let : Algebra L M := i.toRingHom.toAlgebra
  let : IsScalarTower P L M := IsScalarTower.of_algebraMap_eq fun _ => i.commutes _
  let r : (M ≃ₐ[F] M) →* (L ≃ₐ[P] L) :=
    IntermediateField.restrictRestrictAlgEquivMapHom P L F M
  have hr : Function.Injective r := by
    apply (injective_iff_map_eq_one r).mpr
    intro ρ hρ
    have hfix (a : L) : ρ (i a) = i a := by
      have h := AlgEquiv.restrictNormal_commutes
        (MulSemiringAction.toAlgAut (M ≃ₐ[F] M) P M ρ) L a
      change i (r ρ a) = ρ (i a) at h
      rw [hρ, AlgEquiv.one_apply] at h
      exact h.symm
    have hhom : M.val.comp ρ.toAlgHom = M.val := by
      apply IntermediateField.adjoin_algHom_ext F
      intro x hx
      have h := congrArg (fun a : M => (a : k)) (hfix ⟨x, hx⟩)
      exact h
    apply AlgEquiv.ext
    intro a
    apply Subtype.ext
    exact DFunLike.congr_fun hhom a
  rw [← IsGalois.card_aut_eq_finrank F M, ← IsGalois.card_aut_eq_finrank P L]
  exact Subgroup.card_dvd_of_injective r hr

end C3PerfectField
