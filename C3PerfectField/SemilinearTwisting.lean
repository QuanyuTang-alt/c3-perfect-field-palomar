module

public import C3PerfectField.MainStatement
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.RingTheory.Finiteness.Basic

/-!
Manuscript Definition `def:twist` and Lemma `lem:twisting`.
Twisting is restriction of scalars along the inverse ring automorphism.
The scalar action used for dimension is the canonical action induced by
the twisted bundled module, rather than an unrelated action on its carrier.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open CategoryTheory
open scoped ModuleCat

universe u v w

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

/-- Compatibility of a ring automorphism with the indicated field automorphism. -/
def IsSemilinearAlgebraAut (σ : k ≃+* k) (α : A ≃+* A) : Prop :=
  ∀ c : k, α (algebraMap k A c) = algebraMap k A (σ c)

theorem IsSemilinearAlgebraAut.symm {σ : k ≃+* k} {α : A ≃+* A}
    (h : IsSemilinearAlgebraAut σ α) : IsSemilinearAlgebraAut σ.symm α.symm := by
  intro c
  apply α.injective
  rw [α.apply_symm_apply, h (σ.symm c), σ.apply_symm_apply]

theorem IsSemilinearAlgebraAut.smul {σ : k ≃+* k} {α : A ≃+* A}
    (h : IsSemilinearAlgebraAut σ α) (c : k) (a : A) :
    α (c • a) = σ c • α a := by
  simp only [Algebra.smul_def, map_mul]
  rw [h c]

theorem IsSemilinearAlgebraAut.trans {σ τ : k ≃+* k} {α β : A ≃+* A}
    (hα : IsSemilinearAlgebraAut σ α) (hβ : IsSemilinearAlgebraAut τ β) :
    IsSemilinearAlgebraAut (τ.trans σ) (β.trans α) := by
  intro c
  exact (congrArg α (hβ c)).trans (hα (τ c))

/-- The underlying additive group and every morphism remain unchanged. -/
def moduleTwist (α : A ≃+* A) : ModuleCat.{w} A ⥤ ModuleCat.{w} A :=
  ModuleCat.restrictScalars α.symm.toRingHom

@[simp]
theorem moduleTwist_smul (α : A ≃+* A) (M : ModuleCat.{w} A)
    (a : A) (x : (moduleTwist α).obj M) :
    a • x = α.symm a • (show M from x) := rfl

@[simp]
theorem moduleTwist_map_apply (α : A ≃+* A) {M N : ModuleCat.{w} A}
    (f : M ⟶ N) (x : (moduleTwist α).obj M) :
    (moduleTwist α).map f x = f (show M from x) := rfl

instance moduleTwist_additive (α : A ≃+* A) : (moduleTwist.{v, w} α).Additive :=
  inferInstanceAs (ModuleCat.restrictScalars α.symm.toRingHom).Additive

instance moduleTwist_isEquivalence (α : A ≃+* A) :
    (moduleTwist.{v, w} α).IsEquivalence :=
  ModuleCat.restrictScalars_isEquivalence_of_ringEquiv α.symm

instance moduleTwist_preservesFiniteLimits (α : A ≃+* A) :
    Limits.PreservesFiniteLimits (moduleTwist.{v, w} α) :=
  inferInstanceAs (Limits.PreservesFiniteLimits
    (ModuleCat.restrictScalars α.symm.toRingHom))

instance moduleTwist_preservesFiniteColimits (α : A ≃+* A) :
    Limits.PreservesFiniteColimits (moduleTwist.{v, w} α) :=
  inferInstanceAs (Limits.PreservesFiniteColimits
    (ModuleCat.restrictScalars α.symm.toRingHom))

theorem moduleTwist_exact (α : A ≃+* A)
    (S : ShortComplex (ModuleCat.{w} A)) (h : S.Exact) :
    (S.map (moduleTwist α)).Exact :=
  ModuleCat.restrictScalars_map_exact α.symm.toRingHom S h

/-- Identity twisting is naturally the identity by the identity additive map. -/
def moduleTwistId : moduleTwist.{v, w} (RingEquiv.refl A) ≅ 𝟭 _ :=
  ModuleCat.restrictScalarsId A

/-- In `β ⋙ α`, first twist by β and then by α. This is α ∘ β,
written `β.trans α` by the ring-equivalence API. -/
def moduleTwistComp (α β : A ≃+* A) :
    moduleTwist.{v, w} β ⋙ moduleTwist α ≅ moduleTwist (β.trans α) :=
  (ModuleCat.restrictScalarsComp' α.symm.toRingHom β.symm.toRingHom
    (β.trans α).symm.toRingHom rfl).symm

/-- The chosen inverse functor is exactly twisting by the inverse automorphism. -/
def moduleTwistEquivalence (α : A ≃+* A) : ModuleCat.{w} A ≌ ModuleCat.{w} A :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv α.symm

/-- The scalar action induced from the twisted A-module is σ⁻¹ on k. -/
theorem moduleTwist_field_smul {σ : k ≃+* k} {α : A ≃+* A}
    (h : IsSemilinearAlgebraAut σ α) (M : ModuleCat.{w} A)
    (c : k) (x : (moduleTwist α).obj M) :
    c • x = σ.symm c • (show M from x) := by
  change α.symm (algebraMap k A c) • (show M from x) =
    algebraMap k A (σ.symm c) • (show M from x)
  rw [h.symm c]

/-- Rank preservation includes infinite-dimensional modules. -/
theorem moduleTwist_rank {σ : k ≃+* k} {α : A ≃+* A}
    (h : IsSemilinearAlgebraAut σ α) (M : ModuleCat.{w} A) :
    Module.rank k ((moduleTwist α).obj M) = Module.rank k M := by
  apply rank_eq_of_equiv_equiv σ.symm
    (show (moduleTwist α).obj M ≃+ M from AddEquiv.refl M) σ.symm.bijective
  intro c x
  exact moduleTwist_field_smul h M c x

theorem moduleTwist_finrank {σ : k ≃+* k} {α : A ≃+* A}
    (h : IsSemilinearAlgebraAut σ α) (M : ModuleCat.{w} A) :
    Module.finrank k ((moduleTwist α).obj M) = Module.finrank k M := by
  unfold Module.finrank
  rw [moduleTwist_rank h M]

/-- Finiteness is transferred for the actual canonical twisted scalar action. -/
theorem moduleTwist_finite {σ : k ≃+* k} {α : A ≃+* A}
    (h : IsSemilinearAlgebraAut σ α) (M : ModuleCat.{w} A) [Module.Finite k M] :
    Module.Finite k ((moduleTwist α).obj M) := by
  apply Module.finite_of_rank_eq_nat
  rw [moduleTwist_rank h M, ← Module.finrank_eq_rank]

end

end C3PerfectField
