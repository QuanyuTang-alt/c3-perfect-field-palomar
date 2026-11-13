module

public import C3PerfectField.PrimeGaloisOrbits
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
Manuscript Lemma `lem:rational-degree`. Distinct Galois automorphisms
extend fixing the independent parameters and give distinct embeddings of
the compositum. The embedding count and the algebraic adjoin rank bound
prove that its degree is unchanged.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

universe u v

variable {P : Type u} {k : Type v} [Field P] [Field k] [Algebra P k]

/-- Fixing a field and a set fixes the field they generate. -/
theorem fixes_intermediateField_adjoin (σ : k ≃+* k) {s : Set k}
    (hP : ∀ a : P, σ (algebraMap P k a) = algebraMap P k a)
    (hs : ∀ a ∈ s, σ a = a) :
    ∀ a ∈ IntermediateField.adjoin P s, σ a = a := by
  exact IntermediateField.adjoin_le_subfield P s
    (K := RingHom.eqLocusField σ.toRingHom (RingHom.id k))
    (fun _ ⟨a, ha⟩ => ha ▸ hP a) hs

/-- The algebraic compositum has finite degree bounded by the original
finite extension, for an arbitrary change of base in the common overfield. -/
theorem finiteDimensional_adjoin_of_finiteDimensional (L : IntermediateField P k)
    [FiniteDimensional P L] (F : Type v) [Field F] [Algebra P F]
    [Algebra F k] [IsScalarTower P F k] :
    FiniteDimensional F (IntermediateField.adjoin F (L : Set k)) := by
  apply Module.rank_lt_aleph0_iff.mp
  exact lt_of_le_of_lt
    (IntermediateField.adjoin_rank_le_of_isAlgebraic_right F L)
    (Module.rank_lt_aleph0 P L)

theorem finrank_adjoin_le_of_finiteDimensional (L : IntermediateField P k)
    [FiniteDimensional P L] (F : Type v) [Field F] [Algebra P F]
    [Algebra F k] [IsScalarTower P F k] :
    Module.finrank F (IntermediateField.adjoin F (L : Set k)) ≤
      Module.finrank P L := by
  exact Cardinal.toNat_le_toNat
    (IntermediateField.adjoin_rank_le_of_isAlgebraic_right F L)
    (Module.rank_lt_aleph0 P L)

/-- Rational change of base preserves the degree of a finite Galois
subextension. No finiteness of the set of independent parameters is needed. -/
theorem finrank_adjoin_independent_galois [IsAlgClosed k]
    (L : IntermediateField P k) [FiniteDimensional P L] [IsGalois P L]
    {s : Set k} (hs : AlgebraicIndepOn P id s) :
    Module.finrank (IntermediateField.adjoin P s)
      (IntermediateField.adjoin (IntermediateField.adjoin P s) (L : Set k)) =
        Module.finrank P L := by
  classical
  let R := IntermediateField.adjoin P s
  let M := IntermediateField.adjoin R (L : Set k)
  let := finiteDimensional_adjoin_of_finiteDimensional L R
  have hsL : AlgebraicIndepOn L id s := hs.extendScalars L
  have hext (ρ : L ≃ₐ[P] L) :
      ∃ σ : k ≃+* k,
        (∀ a : L, σ (a : k) = (ρ a : k)) ∧
          ∀ a ∈ s, σ a = a :=
    exists_ringEquiv_extension_fixing_independent hsL ρ.toRingEquiv
  let σ (ρ : L ≃ₐ[P] L) := (hext ρ).choose
  have hσ (ρ : L ≃ₐ[P] L) :
      (∀ a : L, σ ρ (a : k) = (ρ a : k)) ∧
        ∀ a ∈ s, σ ρ a = a := (hext ρ).choose_spec
  have hfix (ρ : L ≃ₐ[P] L) : ∀ a ∈ R, σ ρ a = a := by
    apply fixes_intermediateField_adjoin (σ ρ)
    · intro a
      have h := (hσ ρ).1 (algebraMap P L a)
      change σ ρ (algebraMap P k a) = (ρ (algebraMap P L a) : k) at h
      simpa only [ρ.commutes, IntermediateField.coe_algebraMap_apply] using h
    · exact (hσ ρ).2
  let f (ρ : L ≃ₐ[P] L) : M →ₐ[R] k := {
    toRingHom := (σ ρ).toRingHom.comp M.subtype
    commutes' := fun a => hfix ρ a a.2
  }
  have hf : Function.Injective f := by
    intro ρ τ h
    apply AlgEquiv.ext
    intro a
    apply Subtype.ext
    let b : M := ⟨a, IntermediateField.subset_adjoin R (L : Set k) a.2⟩
    have hb := DFunLike.congr_fun h b
    change σ ρ (a : k) = σ τ (a : k) at hb
    simpa only [(hσ ρ).1, (hσ τ).1] using hb
  apply le_antisymm (finrank_adjoin_le_of_finiteDimensional L R)
  calc
    Module.finrank P L = Nat.card (L ≃ₐ[P] L) :=
      (IsGalois.card_aut_eq_finrank P L).symm
    _ ≤ Nat.card (M →ₐ[R] k) := Nat.card_le_card_of_injective f hf
    _ ≤ Module.finrank R M := card_algHom_le_finrank R M k

end C3PerfectField
