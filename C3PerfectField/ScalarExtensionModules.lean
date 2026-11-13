module

public import C3PerfectField.MainStatement
public import C3PerfectField.ScalarExtensionLinear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
Manuscript `def:scalar` on actual module categories: A_K = K ⊗[k] A
acts on X_K = K ⊗[k] X by multiplying the scalar factor and applying
the A-action to the module factor. The functor maps f to id_K ⊗ f.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat TensorProduct

universe u v w

variable {k : Type u} {K : Type w} {A : Type v}
  [Field k] [Field K] [Algebra k K] [Ring A] [Algebra k A]

/-- The scalar-extended algebra representation on the actual tensor space. -/
def scalarExtensionRepresentation (M : ModuleCat.{max u v} A) :
    (K ⊗[k] A) →ₐ[K] Module.End K (K ⊗[k] M) :=
  AlgHom.liftEquiv k K A _
    ((Module.End.baseChangeHom k K M).comp (Algebra.lsmul k k M))

/-- The defining action from the manuscript, on pure tensors. -/
theorem scalarExtensionRepresentation_tmul (M : ModuleCat.{max u v} A)
    (c d : K) (a : A) (x : M) :
    scalarExtensionRepresentation (k := k) (K := K) M (c ⊗ₜ[k] a) (d ⊗ₜ[k] x) =
      (c * d) ⊗ₜ[k] (a • x) := by
  change c • ((Algebra.lsmul k k M a).baseChange K) (d ⊗ₜ[k] x) = _
  rw [LinearMap.baseChange_tmul, Algebra.lsmul_apply, TensorProduct.smul_tmul']
  rfl

/-- The actual X_K as a left A_K-module. -/
def scalarExtensionObject (M : ModuleCat.{max u v} A) :
    ModuleCat.{max u v w} (K ⊗[k] A) :=
  letI := Module.compHom (K ⊗[k] M)
    (scalarExtensionRepresentation (k := k) (K := K) M).toRingHom
  ModuleCat.of (K ⊗[k] A) (K ⊗[k] M)

theorem scalarExtensionObject_smul (M : ModuleCat.{max u v} A)
    (s : K ⊗[k] A) (z : scalarExtensionObject (k := k) (K := K) M) :
    s • z = scalarExtensionRepresentation (k := k) (K := K) M s z := rfl

/-- The scalar action obtained through A_K agrees with the native tensor
K-action. This explicitly resolves the ModuleCat scalar-action issue. -/
def scalarExtensionObjectScalarEquiv (M : ModuleCat.{max u v} A) :
    scalarExtensionObject (k := k) (K := K) M ≃ₗ[K] (K ⊗[k] M) where
  toAddEquiv := AddEquiv.refl _
  map_smul' c z := by
    change scalarExtensionRepresentation (k := k) (K := K) M
      (algebraMap K (K ⊗[k] A) c) z =
        (algebraMap K (Module.End K (K ⊗[k] M)) c) z
    rw [AlgHom.commutes]

@[simp]
theorem scalarExtensionObjectScalarEquiv_apply (M : ModuleCat.{max u v} A)
    (z : scalarExtensionObject (k := k) (K := K) M) :
    scalarExtensionObjectScalarEquiv (k := k) (K := K) M z = z := rfl

theorem finite_scalarExtensionObject (M : ModuleCat.{max u v} A) [Module.Finite k M] :
    Module.Finite K (scalarExtensionObject (k := k) (K := K) M) :=
  Module.Finite.equiv (scalarExtensionObjectScalarEquiv (k := k) (K := K) M).symm

theorem finrank_scalarExtensionObject (M : ModuleCat.{max u v} A) :
    Module.finrank K (scalarExtensionObject (k := k) (K := K) M) = Module.finrank k M :=
  (scalarExtensionObjectScalarEquiv (k := k) (K := K) M).finrank_eq.trans
    finrank_scalarExtension

/-- Scalar extension of an actual A-module morphism. -/
def scalarExtensionMap {M N : ModuleCat.{max u v} A} (f : M ⟶ N) :
    scalarExtensionObject (k := k) (K := K) M ⟶
      scalarExtensionObject (k := k) (K := K) N := by
  letI := Module.compHom (K ⊗[k] M)
    (scalarExtensionRepresentation (k := k) (K := K) M).toRingHom
  letI := Module.compHom (K ⊗[k] N)
    (scalarExtensionRepresentation (k := k) (K := K) N).toRingHom
  exact ModuleCat.ofHom {
    toAddHom := ((f.hom.restrictScalars k).baseChange K).toAddHom
    map_smul' := fun s z => by
      let g := (f.hom.restrictScalars k).baseChange K
      change g (scalarExtensionRepresentation (k := k) (K := K) M s z) =
        scalarExtensionRepresentation (k := k) (K := K) N s (g z)
      induction s using TensorProduct.inductionOn with
      | tmul c a =>
        induction z using TensorProduct.inductionOn with
        | tmul d x =>
          simp only [g, scalarExtensionRepresentation_tmul, LinearMap.baseChange_tmul,
            LinearMap.restrictScalars_apply]
          rw [f.hom.map_smul]
        | add z z' hz hz' =>
          simp only [map_add, hz, hz']
      | add s s' hs hs' =>
        simp only [map_add, LinearMap.add_apply, hs, hs']
  }

@[simp]
theorem scalarExtensionMap_tmul {M N : ModuleCat.{max u v} A} (f : M ⟶ N)
    (c : K) (x : M) :
    scalarExtensionMap (k := k) (K := K) f (c ⊗ₜ[k] x) = c ⊗ₜ[k] f x :=
  LinearMap.baseChange_tmul _ _ _

/-- The manuscript's scalar extension is a functor on the actual categories. -/
def scalarExtensionFunctor :
    ModuleCat.{max u v} A ⥤ ModuleCat.{max u v w} (K ⊗[k] A) where
  obj := scalarExtensionObject (k := k) (K := K)
  map := scalarExtensionMap (k := k) (K := K)
  map_id M := by
    ext z
    change ((LinearMap.id : M →ₗ[k] M).baseChange K) z = z
    rw [LinearMap.baseChange_id]
    rfl
  map_comp f g := by
    ext z
    change ((g.hom.restrictScalars k ∘ₗ f.hom.restrictScalars k).baseChange K) z =
      (g.hom.restrictScalars k).baseChange K ((f.hom.restrictScalars k).baseChange K z)
    rw [LinearMap.baseChange_comp]
    rfl

instance scalarExtensionFunctor_additive :
    (scalarExtensionFunctor (k := k) (K := K) (A := A)).Additive where
  map_add := by
    intro M N f g
    ext z
    change ((f.hom.restrictScalars k + g.hom.restrictScalars k).baseChange K) z = _
    rw [LinearMap.baseChange_add]
    rfl

/-- Faithfulness uses the injectivity of the canonical tensor inclusion,
so it does not need the field extension to be finite. -/
instance scalarExtensionFunctor_faithful :
    (scalarExtensionFunctor (k := k) (K := K) (A := A)).Faithful where
  map_injective := by
    intro M N f g h
    ext x
    have hx := congrArg (fun t => t (1 ⊗ₜ[k] x)) h
    change scalarExtensionMap (k := k) (K := K) f (1 ⊗ₜ[k] x) =
      scalarExtensionMap (k := k) (K := K) g (1 ⊗ₜ[k] x) at hx
    simp only [scalarExtensionMap_tmul] at hx
    exact scalarTensorInclusion_injective (k := k) (K := K) hx

/-- Exactness holds for actual module-category short complexes. -/
theorem scalarExtensionFunctor_exact (S : ShortComplex (ModuleCat.{max u v} A))
    (hS : S.Exact) :
    (S.map (scalarExtensionFunctor (k := k) (K := K))).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact scalarExtension_exact (k := k) (K := K)
    (f := S.f.hom.restrictScalars k) (g := S.g.hom.restrictScalars k) hS

/-- Finite sums, kernels, and cokernels are preserved categorically. -/
theorem scalarExtensionFunctor_preservesFiniteLimitsAndColimits :
    PreservesFiniteLimits (scalarExtensionFunctor (k := k) (K := K) (A := A)) ∧
      PreservesFiniteColimits (scalarExtensionFunctor (k := k) (K := K) (A := A)) :=
  ((Functor.exact_tfae (scalarExtensionFunctor (k := k) (K := K) (A := A))).out 2 4).mp
    (scalarExtensionFunctor_exact (k := k) (K := K))

instance scalarExtensionFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (scalarExtensionFunctor (k := k) (K := K) (A := A)) :=
  (scalarExtensionFunctor_preservesFiniteLimitsAndColimits (k := k) (K := K)).1

instance scalarExtensionFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (scalarExtensionFunctor (k := k) (K := K) (A := A)) :=
  (scalarExtensionFunctor_preservesFiniteLimitsAndColimits (k := k) (K := K)).2

/-- Both endpoints and the middle exactness of a short exact sequence are
preserved by the actual scalar-extension functor. -/
theorem scalarExtensionFunctor_shortExact (S : ShortComplex (ModuleCat.{max u v} A))
    (hS : S.ShortExact) :
    (S.map (scalarExtensionFunctor (k := k) (K := K))).ShortExact :=
  hS.map_of_exact (scalarExtensionFunctor (k := k) (K := K))

variable {L : Type u} [Field L] [Algebra k L]

/-- Scalar extension of the actual finite-module objects used in the main
statement. An algebraic closure can be chosen in the universe of k. -/
def scalarExtensionFiniteModule (M : FiniteModule k A) : FiniteModule L (L ⊗[k] A) := by
  let : Module.Finite k M.val := M.property
  exact ⟨scalarExtensionObject (k := k) (K := L) M.val,
    finite_scalarExtensionObject (k := k) (K := L) M.val⟩

theorem finrank_scalarExtensionFiniteModule (M : FiniteModule k A) :
    Module.finrank L (scalarExtensionFiniteModule (L := L) M).val =
      Module.finrank k M.val :=
  finrank_scalarExtensionObject (k := k) (K := L) M.val

end

end C3PerfectField
