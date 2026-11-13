module

public import C3PerfectField.GaloisTensorDescent
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
Elementary scalar extension and the subspace descent correspondence.
Kernels, quotients, exactness, and dimensions refer to the actual tensor
maps, not to an abstract surrogate. The canonical inclusion is also the
inverse used by the invariant-subspace correspondence.
-/

@[expose] public section

namespace C3PerfectField

noncomputable section

open Module
open scoped TensorProduct

universe u v w t s

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
  {V : Type w} {U : Type t} {Z : Type s}
  [AddCommGroup V] [Module k V] [AddCommGroup U] [Module k U]
  [AddCommGroup Z] [Module k Z]

/-- Scalar extension preserves the dimension of a vector space. -/
theorem finrank_scalarExtension : Module.finrank K (K ⊗[k] V) = Module.finrank k V :=
  Module.finrank_baseChange

/-- Finite-dimensional vector spaces remain finite-dimensional after
scalar extension, even when K/k is infinite. -/
theorem finite_scalarExtension [FiniteDimensional k V] :
    FiniteDimensional K (K ⊗[k] V) := inferInstance

/-- Scalar extension detects the zero vector space. -/
theorem scalarExtension_subsingleton_iff :
    Subsingleton (K ⊗[k] V) ↔ Subsingleton V := by
  constructor
  · intro h
    let := h
    exact Function.Injective.subsingleton
      (scalarTensorInclusion_injective (k := k) (K := K) (V := V))
  · intro h
    let := h
    infer_instance

/-- The actual maps id_K ⊗ f and id_K ⊗ g preserve exactness. -/
theorem scalarExtension_exact {f : U →ₗ[k] V} {g : V →ₗ[k] Z}
    (h : Function.Exact f g) :
    Function.Exact (f.baseChange K) (g.baseChange K) :=
  Module.Flat.lTensor_exact K h

/-- Scalar extension preserves monomorphisms. -/
theorem scalarExtension_injective (f : U →ₗ[k] V) (hf : Function.Injective f) :
    Function.Injective (f.baseChange K) :=
  Module.Flat.lTensor_preserves_injective_linearMap f hf

/-- Scalar extension preserves epimorphisms. -/
theorem scalarExtension_surjective (f : U →ₗ[k] V) (hf : Function.Surjective f) :
    Function.Surjective (f.baseChange K) :=
  f.baseChange_surjective K hf

/-- The kernel of the actual scalar-extended map is the canonical image of
the tensor product of its original kernel. -/
theorem scalarExtension_ker (f : U →ₗ[k] V) :
    (f.baseChange K).ker = f.ker.baseChange K := by
  change (f.baseChange K).ker = LinearMap.range (f.ker.subtype.baseChange K)
  rw [← LinearMap.exact_iff]
  exact scalarExtension_exact f.exact_subtype_ker_map

/-- The scalar-extended quotient map has exactly the expected kernel. -/
theorem scalarExtension_quotient_ker (p : Submodule k V) :
    (p.mkQ.baseChange K).ker = p.baseChange K := by
  rw [scalarExtension_ker, Submodule.ker_mkQ]

/-- Flat scalar extension commutes with inverse images of subspaces. -/
theorem scalarExtension_comap (p : Submodule k V) (f : U →ₗ[k] V) :
    (p.comap f).baseChange K = (p.baseChange K).comap (f.baseChange K) := by
  rw [← scalarExtension_quotient_ker p, ← LinearMap.ker_comp,
    ← LinearMap.baseChange_comp, scalarExtension_ker,
    LinearMap.ker_comp, Submodule.ker_mkQ]

/-- The quotient commutes with scalar extension as a K-linear equivalence. -/
def scalarExtensionQuotientEquiv (p : Submodule k V) :
    ((K ⊗[k] V) ⧸ p.baseChange K) ≃ₗ[K] K ⊗[k] (V ⧸ p) :=
  (Submodule.quotEquivOfEq _ _ (scalarExtension_quotient_ker p).symm).trans
    ((p.mkQ.baseChange K).quotKerEquivOfSurjective
      (scalarExtension_surjective p.mkQ p.mkQ_surjective))

/-- This equivalence is the canonical one induced by id_K ⊗ mkQ. -/
theorem scalarExtensionQuotientEquiv_mk (p : Submodule k V) (c : K) (x : V) :
    scalarExtensionQuotientEquiv p (Submodule.Quotient.mk (c ⊗ₜ[k] x)) =
      c ⊗ₜ[k] (p.mkQ x) := by
  simp [scalarExtensionQuotientEquiv, LinearMap.quotKerEquivOfSurjective_apply_mk,
    LinearMap.baseChange_tmul]

/-- Pullback along the canonical tensor inclusion recovers the original
subspace, for any field extension. -/
theorem descendedTensorSubspace_baseChange (p : Submodule k V) :
    descendedTensorSubspace (p.baseChange K) = p := by
  ext x
  change 1 ⊗ₜ[k] x ∈ p.baseChange K ↔ x ∈ p
  rw [← scalarExtension_quotient_ker, LinearMap.mem_ker, LinearMap.baseChange_tmul]
  constructor
  · intro hx
    have hx' : p.mkQ x = 0 :=
      scalarTensorInclusion_injective (k := k) (K := K)
        (by simpa only [TensorProduct.mk_apply, TensorProduct.tmul_zero] using hx)
    simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hx'
  · intro hx
    have hx' : p.mkQ x = 0 := by
      simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using hx
    rw [hx', TensorProduct.tmul_zero]

/-- The image of K ⊗ W₀ has its expected vector space structure. -/
def descendedTensorSubspaceEquiv (G : Subgroup (K ≃ₐ[k] K))
    [FiniteDimensional k V]
    (hG : ∀ x : K, (∀ σ : G, σ.val x = x) → ∃ c : k, algebraMap k K c = x)
    (W : Submodule K (K ⊗[k] V))
    (hW : ∀ (σ : G) (z : K ⊗[k] V), z ∈ W → tensorGaloisAction σ.val z ∈ W) :
    (K ⊗[k] descendedTensorSubspace W) ≃ₗ[K] W :=
  (Submodule.toBaseChange.toLinearEquiv K (descendedTensorSubspace W)).trans
    (LinearEquiv.ofEq _ _ (tensor_subspace_descent G hG W hW).symm)

/-- The invariant K-subspaces, with their inherited inclusion order. -/
abbrev InvariantTensorSubspace (G : Subgroup (K ≃ₐ[k] K)) :=
  {W : Submodule K (K ⊗[k] V) //
    ∀ (σ : G) (z : K ⊗[k] V), z ∈ W → tensorGaloisAction σ.val z ∈ W}

/-- Galois descent is an order isomorphism between base-field subspaces and
invariant tensor subspaces, not merely existence of some descended space. -/
def tensorSubspaceDescentOrderIso (G : Subgroup (K ≃ₐ[k] K))
    [FiniteDimensional k V]
    (hG : ∀ x : K, (∀ σ : G, σ.val x = x) → ∃ c : k, algebraMap k K c = x) :
    Submodule k V ≃o InvariantTensorSubspace (V := V) G where
  toFun p := ⟨p.baseChange K, fun σ z hz => tensorGaloisAction_mem_baseChange σ.val p z hz⟩
  invFun W := descendedTensorSubspace W.val
  left_inv p := descendedTensorSubspace_baseChange p
  right_inv W := Subtype.ext (tensor_subspace_descent G hG W.val W.property).symm
  map_rel_iff' {p q} := by
    change p.baseChange K ≤ q.baseChange K ↔ p ≤ q
    constructor
    · intro hpq x hx
      have h : 1 ⊗ₜ[k] x ∈ q.baseChange K := hpq (p.tmul_mem_baseChange_of_mem 1 hx)
      have hx' : x ∈ descendedTensorSubspace (q.baseChange K) := h
      simpa only [descendedTensorSubspace_baseChange] using hx'
    · exact Submodule.baseChange_mono K

end

end C3PerfectField
