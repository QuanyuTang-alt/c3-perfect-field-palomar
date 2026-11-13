module

public import C3PerfectField.ScalarExtensionModules
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
The coefficient Galois action on A_K and X_K. The actual algebra and
module actions intertwine, so invariance is compatible with the scalar
extension of module morphisms.
-/

@[expose] public section

namespace C3PerfectField

noncomputable section

open CategoryTheory
open scoped ModuleCat TensorProduct

universe u v w

variable {k : Type u} {K : Type w} {A : Type v}
  [Field k] [Field K] [Algebra k K] [Ring A] [Algebra k A]

/-- The actual coefficient automorphism of A_K. -/
def scalarExtensionAlgebraAut (σ : K ≃ₐ[k] K) :
    (K ⊗[k] A) ≃ₐ[k] (K ⊗[k] A) :=
  Algebra.TensorProduct.congr σ (AlgEquiv.refl : A ≃ₐ[k] A)

@[simp]
theorem scalarExtensionAlgebraAut_tmul (σ : K ≃ₐ[k] K) (c : K) (a : A) :
    scalarExtensionAlgebraAut (A := A) σ (c ⊗ₜ[k] a) = σ c ⊗ₜ[k] a := by
  simp [scalarExtensionAlgebraAut, Algebra.TensorProduct.congr_apply]

/-- The coefficient automorphism is precisely the tensor action on A. -/
theorem scalarExtensionAlgebraAut_eq_tensorGaloisAction (σ : K ≃ₐ[k] K)
    (s : K ⊗[k] A) :
    scalarExtensionAlgebraAut (A := A) σ s = tensorGaloisAction σ s := by
  induction s using TensorProduct.inductionOn with
  | tmul c a => simp only [scalarExtensionAlgebraAut_tmul, tensorGaloisAction_tmul]
  | add s s' hs hs' => simp only [map_add, hs, hs']

/-- The actual Galois action on tensors intertwines the actual A_K-action
with the coefficient automorphism of A_K. -/
theorem tensorGaloisAction_representation (M : ModuleCat.{max u v} A)
    (σ : K ≃ₐ[k] K) (s : K ⊗[k] A) (z : K ⊗[k] M) :
    tensorGaloisAction σ (scalarExtensionRepresentation (k := k) M s z) =
      scalarExtensionRepresentation (k := k) M
        (scalarExtensionAlgebraAut σ s) (tensorGaloisAction σ z) := by
  induction s using TensorProduct.inductionOn with
  | tmul c a =>
    induction z using TensorProduct.inductionOn with
    | tmul d x =>
      simp only [scalarExtensionRepresentation_tmul, tensorGaloisAction_tmul,
        scalarExtensionAlgebraAut_tmul, map_mul]
    | add z z' hz hz' =>
      simp only [map_add, hz, hz']
  | add s s' hs hs' =>
    simp only [map_add, LinearMap.add_apply, hs, hs']

/-- The semilinear module law in the bundled scalar-extended object, with
the native coefficient action transported through the checked scalar
equivalence. -/
theorem tensorGaloisAction_scalarExtension_smul (M : ModuleCat.{max u v} A)
    (σ : K ≃ₐ[k] K) (s : K ⊗[k] A)
    (z : scalarExtensionObject (k := k) (K := K) M) :
    tensorGaloisAction σ
      (scalarExtensionObjectScalarEquiv (k := k) (K := K) M (s • z)) =
        scalarExtensionObjectScalarEquiv (k := k) (K := K) M
          (scalarExtensionAlgebraAut σ s •
            (scalarExtensionObjectScalarEquiv (k := k) (K := K) M).symm
              (tensorGaloisAction σ
                (scalarExtensionObjectScalarEquiv (k := k) (K := K) M z))) :=
  tensorGaloisAction_representation M σ s z

/-- Scalar extension of an A-module map commutes with coefficient action. -/
theorem scalarExtensionMap_galois {M N : ModuleCat.{max u v} A} (f : M ⟶ N)
    (σ : K ≃ₐ[k] K) (z : K ⊗[k] M) :
    scalarExtensionMap (k := k) (K := K) f (tensorGaloisAction σ z) =
      tensorGaloisAction σ (scalarExtensionMap (k := k) (K := K) f z) := by
  change (f.hom.restrictScalars k).baseChange K (tensorGaloisAction σ z) =
    tensorGaloisAction σ ((f.hom.restrictScalars k).baseChange K z)
  induction z using TensorProduct.inductionOn with
  | tmul c x => simp only [tensorGaloisAction_tmul, LinearMap.baseChange_tmul]
  | add z z' hz hz' => simp only [map_add, hz, hz']

/-- An A_K-stable tensor subspace descends to an actual A-submodule. Here
stability is expressed by the A-generators of A_K. -/
def descendedModuleSubspace (M : ModuleCat.{max u v} A)
    (W : Submodule K (K ⊗[k] M))
    (hWA : ∀ (a : A) (z : K ⊗[k] M), z ∈ W →
      scalarExtensionRepresentation (k := k) M (1 ⊗ₜ[k] a) z ∈ W) :
    Submodule A M where
  carrier := {x | (1 : K) ⊗ₜ[k] x ∈ W}
  zero_mem' := by
    change (1 : K) ⊗ₜ[k] (0 : M) ∈ W
    simpa only [TensorProduct.tmul_zero] using W.zero_mem
  add_mem' := by
    intro x y hx hy
    change (1 : K) ⊗ₜ[k] (x + y) ∈ W
    simpa only [TensorProduct.tmul_add] using W.add_mem hx hy
  smul_mem' a x hx := by
    change (1 : K) ⊗ₜ[k] (a • x) ∈ W
    have h := hWA a (1 ⊗ₜ[k] x) hx
    simpa only [scalarExtensionRepresentation_tmul, one_mul] using h

/-- The descended A-submodule has exactly the k-vector subspace W₀
specified in the manuscript. -/
theorem descendedModuleSubspace_restrictScalars (M : ModuleCat.{max u v} A)
    (W : Submodule K (K ⊗[k] M))
    (hWA : ∀ (a : A) (z : K ⊗[k] M), z ∈ W →
      scalarExtensionRepresentation (k := k) M (1 ⊗ₜ[k] a) z ∈ W) :
    (descendedModuleSubspace M W hWA).restrictScalars k = descendedTensorSubspace W := by
  ext x
  rfl

/-- The scalar extension of this genuine A-submodule recovers W. -/
theorem tensor_module_subspace_descent (M : ModuleCat.{max u v} A) [Module.Finite k M]
    (G : Subgroup (K ≃ₐ[k] K))
    (hG : ∀ x : K, (∀ σ : G, σ.val x = x) → ∃ c : k, algebraMap k K c = x)
    (W : Submodule K (K ⊗[k] M))
    (hWA : ∀ (a : A) (z : K ⊗[k] M), z ∈ W →
      scalarExtensionRepresentation (k := k) M (1 ⊗ₜ[k] a) z ∈ W)
    (hW : ∀ (σ : G) (z : K ⊗[k] M), z ∈ W → tensorGaloisAction σ.val z ∈ W) :
    W = ((descendedModuleSubspace M W hWA).restrictScalars k).baseChange K := by
  rw [descendedModuleSubspace_restrictScalars]
  exact tensor_subspace_descent G hG W hW

end

end C3PerfectField
