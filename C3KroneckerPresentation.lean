module

public import C3Kronecker
public import Mathlib.LinearAlgebra.Prod

/-!
A literal short exact presentation of the regular Kronecker family. The
relation vector is (-lambda,1) and the quotient map is (x,y) ↦ x+lambda*y.
This is a source-level bridge for exact representation embeddings, not the
unconditional C3 theorem.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace C3Kronecker

open CategoryTheory Limits
open LargeIndecomposable LargeIndecomposable.Statement WalkingParallelPair
universe u
variable {k : Type u} [Field k]

abbrev simpleTarget (k : Type u) [Field k] : D k :=
  ⟨Kron.mk (ModuleCat.of k PUnit.{u+1}) (ModuleCat.of k k) 0 0, by
    rw [inD_iff]
    intro v _ _
    rfl⟩

abbrev projectivePair (k : Type u) [Field k] : D k :=
  ⟨Kron.mk (ModuleCat.of k k) (ModuleCat.of k (k × k))
    (ModuleCat.ofHom (LinearMap.inl k k k))
    (ModuleCat.ofHom (LinearMap.inr k k k)), by
    rw [inD_iff]
    intro v hv _
    exact congrArg Prod.fst hv⟩

/-- The actual relation morphism with vector (-lambda,1). -/
abbrev relation (lambda : k) : simpleTarget k ⟶ projectivePair k :=
  ObjectProperty.homMk (Kron.homMk 0
    (ModuleCat.ofHom ((-lambda • (LinearMap.inl k k k)) + (LinearMap.inr k k k)))
    (by ext x; cases x; simp) (by ext x; cases x; simp))

/-- The actual quotient morphism with first component the identity. -/
abbrev projection (lambda : k) : projectivePair k ⟶ regular lambda :=
  ObjectProperty.homMk (Kron.homMk (𝟙 _)
    (ModuleCat.ofHom ((LinearMap.fst k k k) + lambda • (LinearMap.snd k k k)))
    (by apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; simp)
    (by apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; simp))

/-- The two fixed modules in the presentation are finite-dimensional. -/
theorem presentation_finite :
    (simpleTarget k).obj.IsFiniteDimensional ∧ (projectivePair k).obj.IsFiniteDimensional := by
  change (FiniteDimensional k PUnit ∧ FiniteDimensional k k) ∧
    (FiniteDimensional k k ∧ FiniteDimensional k (k × k))
  exact ⟨⟨inferInstance, inferInstance⟩, ⟨inferInstance, inferInstance⟩⟩

/-- Exactness is proved from the literal two coordinate maps. -/
theorem presentation_shortExact (lambda : k) :
    Kron.IsShortExact (relation lambda).hom (projection lambda).hom := by
  intro j
  cases j with
  | zero =>
    constructor
    · intro x y _
      cases x; cases y; rfl
    constructor
    · intro x; exact ⟨x, rfl⟩
    · ext x
      constructor
      · rintro ⟨y, rfl⟩; cases y; rfl
      · intro hx
        change x = 0 at hx
        exact ⟨0, hx.symm⟩
  | one =>
    constructor
    · intro x y hxy
      have h := congrArg Prod.snd hxy
      simpa [relation, Kron.homMk, parallelPairHomMk, ObjectProperty.homMk] using h
    constructor
    · intro x; exact ⟨(x, 0), by simp [projection]⟩
    · ext x
      constructor
      · rintro ⟨y, rfl⟩
        simp [relation, projection, Kron.homMk, parallelPairHomMk,
          ObjectProperty.homMk]
      · intro hx
        change x.1 + lambda * x.2 = 0 at hx
        refine ⟨x.2, ?_⟩
        apply Prod.ext
        · have he : -lambda * x.2 = x.1 :=
            (neg_mul lambda x.2).trans (eq_neg_of_add_eq_zero_left hx).symm
          simpa [relation, Kron.homMk, parallelPairHomMk, ObjectProperty.homMk] using he
        · simp [relation, Kron.homMk, parallelPairHomMk, ObjectProperty.homMk]

/-- The relation is affine in the parameter in the actual hom space. -/
theorem relation_affine (lambda : k) :
    relation lambda = relation (0 : k) - lambda •
      ObjectProperty.homMk (Kron.homMk 0
        (ModuleCat.ofHom (LinearMap.inl k k k))
        (by ext x; cases x; simp) (by ext x; cases x; simp)) := by
  let E : (simpleTarget k ⟶ projectivePair k) ≃ₗ[k]
      ((simpleTarget k).obj ⟶ (projectivePair k).obj) :=
    InducedCategory.homLinearEquiv
  have hE (f : simpleTarget k ⟶ projectivePair k) : E f = f.hom := rfl
  apply E.injective
  rw [map_sub, map_smul, hE, hE, hE]
  apply Kron.hom_ext
  · apply ModuleCat.hom_ext
    change (0 : PUnit →ₗ[k] k) = 0 - lambda • (0 : PUnit →ₗ[k] k)
    simp only [smul_zero, sub_zero]
  · apply ModuleCat.hom_ext
    simp only [relation, ObjectProperty.homMk, Kron.homMk, parallelPairHomMk,
      NatTrans.app_sub, NatTrans.app_smul, ModuleCat.hom_sub, ModuleCat.hom_smul,
      ModuleCat.hom_ofHom]
    change (-lambda • LinearMap.inl k k k + LinearMap.inr k k k) =
      (-(0 : k)) • LinearMap.inl k k k + LinearMap.inr k k k -
        lambda • LinearMap.inl k k k
    simp only [neg_zero, zero_smul, zero_add, sub_eq_add_neg]
    apply LinearMap.ext
    intro (x : k)
    apply Prod.ext <;> simp [LinearMap.inl_apply, LinearMap.inr_apply,
      LinearMap.smul_apply, LinearMap.add_apply]
end C3Kronecker
