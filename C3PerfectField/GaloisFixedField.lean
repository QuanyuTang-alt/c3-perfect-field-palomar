module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.Pi

/-!
Fixed scalars and fixed coordinate vectors for Galois descent. In particular,
the manuscript's fixed-field lemma follows from perfection and the algebraic
closure assumptions alone, including in positive characteristic.
-/

@[expose] public section

namespace C3PerfectField

noncomputable section

universe u v w

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- Normality of an algebraic closure and separability over a perfect field
together give the infinite Galois extension used below. -/
theorem algebraicClosure_isGalois [PerfectField k] [IsAlgClosure k K] :
    IsGalois k K := {}

/-- Manuscript `lem:fixed-field`; no finite-degree hypothesis is used. -/
theorem algebraicClosure_fixedField [PerfectField k] [IsAlgClosure k K] :
    IntermediateField.fixedField (⊤ : Subgroup (K ≃ₐ[k] K)) = ⊥ := by
  let := algebraicClosure_isGalois (k := k) (K := K)
  exact InfiniteGalois.fixedField_bot

/-- A scalar of an algebraic closure is defined over the perfect base field
exactly when all base-field automorphisms fix it. -/
theorem algebraicClosure_fixed_iff [PerfectField k] [IsAlgClosure k K] (x : K) :
    (∀ σ : K ≃ₐ[k] K, σ x = x) ↔ ∃ c : k, algebraMap k K c = x := by
  let := algebraicClosure_isGalois (k := k) (K := K)
  exact (InfiniteGalois.mem_range_algebraMap_iff_fixed x).symm

/-- The subgroup fixed-field equality used in the manuscript gives exactly
the fixed-scalar criterion needed in the descent theorems. -/
theorem subgroup_fixed_iff (G : Subgroup (K ≃ₐ[k] K))
    (hG : IntermediateField.fixedField G = ⊥) (x : K) :
    (∀ σ : G, σ.val x = x) ↔ ∃ c : k, algebraMap k K c = x := by
  constructor
  · intro hx
    have hmem : x ∈ IntermediateField.fixedField G := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ hσ
      exact hx ⟨σ, hσ⟩
    rw [hG] at hmem
    exact IntermediateField.mem_bot.mp hmem
  · rintro ⟨c, rfl⟩ σ
    exact σ.val.commutes c

variable (k K) (ι : Type w)

/-- The coordinate form of the inclusion of a base-field vector space. -/
def coordinateScalarInclusion : (ι → k) →ₗ[k] (ι → K) where
  toFun x i := algebraMap k K (x i)
  map_add' x y := by ext i; exact map_add _ _ _
  map_smul' c x := by ext i; simp [Algebra.smul_def]

variable {k K ι}

@[simp]
theorem coordinateScalarInclusion_apply (x : ι → k) (i : ι) :
    coordinateScalarInclusion k K ι x i = algebraMap k K (x i) := rfl

theorem coordinateScalarInclusion_injective :
    Function.Injective (coordinateScalarInclusion k K ι) := by
  intro x y h
  ext i
  exact (algebraMap k K).injective (congrFun h i)

/-- Coordinatewise automorphism action, viewed as a k-linear equivalence. -/
def coordinateGaloisAction (σ : K ≃ₐ[k] K) : (ι → K) ≃ₗ[k] (ι → K) where
  toFun x i := σ (x i)
  invFun x i := σ.symm (x i)
  left_inv x := by ext i; exact σ.symm_apply_apply _
  right_inv x := by ext i; exact σ.apply_symm_apply _
  map_add' x y := by ext i; exact map_add _ _ _
  map_smul' c x := by ext i; exact σ.toLinearEquiv.map_smul c (x i)

@[simp]
theorem coordinateGaloisAction_apply (σ : K ≃ₐ[k] K) (x : ι → K) (i : ι) :
    coordinateGaloisAction σ x i = σ (x i) := rfl

@[simp]
theorem coordinateGaloisAction_inclusion (σ : K ≃ₐ[k] K) (x : ι → k) :
    coordinateGaloisAction σ (coordinateScalarInclusion k K ι x) =
      coordinateScalarInclusion k K ι x := by
  ext i
  exact σ.commutes (x i)

/-- Fixed vectors descend coordinatewise for any subgroup with fixed field k.
The coordinate index need not be finite for this assertion. -/
theorem coordinate_fixed_iff (G : Subgroup (K ≃ₐ[k] K))
    (hG : ∀ x : K, (∀ σ : G, σ.val x = x) → ∃ c : k, algebraMap k K c = x)
    (x : ι → K) :
    (∀ σ : G, coordinateGaloisAction σ.val x = x) ↔
      ∃ y : ι → k, coordinateScalarInclusion k K ι y = x := by
  constructor
  · intro hx
    have hi (i : ι) : ∃ c : k, algebraMap k K c = x i :=
      hG (x i) (fun σ => congrFun (hx σ) i)
    choose y hy using hi
    exact ⟨y, funext hy⟩
  · rintro ⟨y, rfl⟩ σ
    exact coordinateGaloisAction_inclusion σ.val y

/-- Fixed coordinate vectors over the algebraic closure of a perfect field
are precisely vectors whose coordinates lie in the base field. -/
theorem algebraicClosure_coordinate_fixed_iff [PerfectField k] [IsAlgClosure k K]
    (x : ι → K) :
    (∀ σ : K ≃ₐ[k] K, coordinateGaloisAction σ x = x) ↔
      ∃ y : ι → k, coordinateScalarInclusion k K ι y = x := by
  constructor
  · intro hx
    have hi (i : ι) : ∃ c : k, algebraMap k K c = x i :=
      (algebraicClosure_fixed_iff (x i)).mp (fun σ => congrFun (hx σ) i)
    choose y hy using hi
    exact ⟨y, funext hy⟩
  · rintro ⟨y, rfl⟩ σ
    exact coordinateGaloisAction_inclusion σ y

end

end C3PerfectField
