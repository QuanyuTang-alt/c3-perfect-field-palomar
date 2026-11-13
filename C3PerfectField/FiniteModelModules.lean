module

public import C3PerfectField.FiniteModelLinear
public import C3PerfectField.SeparableScalarExtension
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
Manuscript `lem:finite-model` in the actual module category. The
coefficient subspace is made into an A-module with its commuting L-action.
Its relative extension is identified with the original A_K-module.
For a perfect base field this also proves the first assertion of
`lem:summand-descent`, by composing with the separable tensor retract.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open CategoryTheory
open scoped ModuleCat TensorProduct

universe u v w

variable {k K : Type u} {A : Type v}
  [Field k] [Field K] [Algebra k K] [Ring A] [Algebra k A]
  (N : ModuleCat.{max u v} (K ⊗[k] A))
  {κ : Type w} [Fintype κ] (b : Module.Basis κ K N)
  (L : IntermediateField k K)

/-- Both scalar actions on an A_K-module are restrictions of its A_K-action. -/
instance finiteModelOriginalTower : IsScalarTower k K N :=
  IsScalarTower.of_algebraMap_smul fun c x => by
    change algebraMap K (K ⊗[k] A) (algebraMap k K c) • x =
      algebraMap k (K ⊗[k] A) c • x
    rw [← IsScalarTower.algebraMap_apply k K (K ⊗[k] A)]

/-- Restrict the original extended-algebra representation along A → A_K. -/
def finiteModelOriginalRepresentation : A →ₐ[k] Module.End K N :=
  (AlgHom.liftEquiv k K A (Module.End K N)).symm
    (Algebra.lsmul K K N (A := K ⊗[k] A))

variable (h : ∀ a x, x ∈ basisModelSubspace b L →
  finiteModelOriginalRepresentation N a x ∈ basisModelSubspace b L)

/-- The coefficient model restricted to the original algebra A. -/
def finiteModelRestrictionObject : ModuleCat.{max u v} A :=
  letI := Module.compHom (basisModelSubspace b L)
    (basisModelAction b L (finiteModelOriginalRepresentation N) h).toRingHom
  ModuleCat.of A (basisModelSubspace b L)

instance finiteModelRestrictionModule :
    Module L (finiteModelRestrictionObject N b L h) :=
  inferInstanceAs (Module L (basisModelSubspace b L))

instance finiteModelRestrictionTower :
    IsScalarTower k L (finiteModelRestrictionObject N b L h) :=
  IsScalarTower.of_algebraMap_smul fun c x => by
    change (algebraMap k L c) • x =
      basisModelAction b L (finiteModelOriginalRepresentation N) h (algebraMap k A c) x
    rw [AlgHom.commutes]
    rfl

instance finiteModelRestrictionComm :
    SMulCommClass A L (finiteModelRestrictionObject N b L h) where
  smul_comm a c x := by
    change basisModelAction b L (finiteModelOriginalRepresentation N) h a (c • x) =
      c • basisModelAction b L (finiteModelOriginalRepresentation N) h a x
    exact map_smul _ _ _

/-- Finiteness of the coefficient model for the L-action used in descent. -/
theorem finite_finiteModelRestrictionObject_L :
    Module.Finite L (finiteModelRestrictionObject N b L h) :=
  finite_basisModelSubspace b L

/-- Restriction from a finite intermediate extension gives a finite A-module. -/
theorem finite_finiteModelRestrictionObject [Module.Finite k L] :
    Module.Finite k (finiteModelRestrictionObject N b L h) := by
  let := finite_finiteModelRestrictionObject_L N b L h
  exact Module.Finite.trans L _

/-- The coefficient model with its full A_L-action. -/
def finiteModelObject : ModuleCat.{max u v} (L ⊗[k] A) :=
  letI := Module.compHom (basisModelSubspace b L)
    (AlgHom.liftEquiv k L A (Module.End L (basisModelSubspace b L))
      (basisModelAction b L (finiteModelOriginalRepresentation N) h)).toRingHom
  ModuleCat.of (L ⊗[k] A) (basisModelSubspace b L)

/-- The L-action induced through A_L agrees with the coefficient-space action. -/
def finiteModelObjectScalarEquiv :
    finiteModelObject N b L h ≃ₗ[L] basisModelSubspace b L where
  toAddEquiv := AddEquiv.refl _
  map_smul' c x := by
    let ρL : (L ⊗[k] A) →ₐ[L] Module.End L (basisModelSubspace b L) :=
      AlgHom.liftEquiv k L A _
        (basisModelAction b L (finiteModelOriginalRepresentation N) h)
    change ρL (c ⊗ₜ[k] (1 : A)) (show basisModelSubspace b L from x) =
      c • (show basisModelSubspace b L from x)
    rw [AlgHom.liftEquiv_tmul, map_one]
    rfl

/-- The actual finite A_L-module furnished by the action coefficients. -/
def finiteModelFiniteModule : FiniteModule L (L ⊗[k] A) := by
  letI := finite_basisModelSubspace b L
  exact ⟨finiteModelObject N b L h,
    Module.Finite.equiv (finiteModelObjectScalarEquiv N b L h).symm⟩

/-- Restriction of the full A_L-model gives the A-module used in the retract. -/
def finiteModelRestrictionIso :
    (ModuleCat.restrictScalars
      (Algebra.TensorProduct.includeRight : A →ₐ[k] L ⊗[k] A).toRingHom).obj
        (finiteModelObject N b L h) ≅ finiteModelRestrictionObject N b L h := by
  let e :
      (ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight : A →ₐ[k] L ⊗[k] A).toRingHom).obj
          (finiteModelObject N b L h) ≃ₗ[A] finiteModelRestrictionObject N b L h := {
    toAddEquiv := AddEquiv.refl _
    map_smul' a x := by
      change AlgHom.liftEquiv k L A (Module.End L (basisModelSubspace b L))
          (basisModelAction b L (finiteModelOriginalRepresentation N) h)
          (1 ⊗ₜ[k] a) x =
        basisModelAction b L (finiteModelOriginalRepresentation N) h a x
      rw [AlgHom.liftEquiv_tmul, one_smul]
  }
  exact e.toModuleIso

/-- The action on the recovered vector space is exactly the original action. -/
theorem finiteModelOriginalRepresentation_lift :
    AlgHom.liftEquiv k K A (Module.End K N) (finiteModelOriginalRepresentation N) =
      Algebra.lsmul K K N (A := K ⊗[k] A) := by
  exact (AlgHom.liftEquiv k K A (Module.End K N)).apply_symm_apply _

/-- Recovery of the full A_K-module, rather than only its underlying vectors. -/
def finiteModelRecoveryIso :
    relativeScalarExtensionObject (k := k) (K := K) (L := L)
      (finiteModelRestrictionObject N b L h) ≅ N := by
  letI := Module.compHom (K ⊗[L] finiteModelRestrictionObject N b L h)
    (relativeScalarExtensionRepresentation (k := k) (K := K) (L := L)
      (finiteModelRestrictionObject N b L h)).toRingHom
  let e : relativeScalarExtensionObject (k := k) (K := K) (L := L)
      (finiteModelRestrictionObject N b L h) ≃ₗ[K ⊗[k] A] N := {
    toAddEquiv := (basisModelExtensionEquiv b L).toAddEquiv
    map_smul' := fun s z => by
      change basisModelExtensionEquiv b L
          (basisModelTensorRepresentation b L (finiteModelOriginalRepresentation N) h s z) =
        s • basisModelExtensionEquiv b L z
      rw [basisModelExtensionEquiv_algebraAction, finiteModelOriginalRepresentation_lift]
      rfl
  }
  exact e.toModuleIso

variable [Module.Finite k A] [Algebra.IsAlgebraic k K]

/-- Every actual finite A_K-module has a finite coefficient model whose
relative tensor extension is isomorphic to that original module. -/
theorem exists_finiteModel_module (N : FiniteModule K (K ⊗[k] A)) :
    ∃ (L : IntermediateField k K) (_ : Module.Finite k L)
      (b : Module.Basis (Fin (Module.finrank K N.val)) K N.val)
      (h : ∀ a x, x ∈ basisModelSubspace b L →
        finiteModelOriginalRepresentation N.val a x ∈ basisModelSubspace b L),
      Nonempty (relativeScalarExtensionObject (k := k) (K := K) (L := L)
        (finiteModelRestrictionObject N.val b L h) ≅ N.val) := by
  let := N.property
  let b := Module.finBasis K N.val
  obtain ⟨L, hL, h⟩ := exists_finite_basisModel b (Module.finBasis k A)
    (finiteModelOriginalRepresentation N.val)
  exact ⟨L, hL, b, h, ⟨finiteModelRecoveryIso N.val b L h⟩⟩

variable [PerfectField k] [IsSepClosed K]

/-- Manuscript `lem:summand-descent`, first assertion: every finite extended
module is an actual direct summand of the extension of a finite base module. -/
theorem exists_scalarExtension_retract (N : FiniteModule K (K ⊗[k] A)) :
    ∃ W : FiniteModule k A,
      Nonempty (Retract N.val (scalarExtensionFiniteModule (L := K) W).val) := by
  obtain ⟨L, hL, b, h, ⟨e⟩⟩ := exists_finiteModel_module N
  let := hL
  let M := finiteModelRestrictionObject N.val b L h
  let W : FiniteModule k A := ⟨M, finite_finiteModelRestrictionObject N.val b L h⟩
  exact ⟨W, ⟨(Retract.ofIso e.symm).trans
    (relativeScalarExtension_retract (k := k) (K := K) (L := L) M)⟩⟩

end

end C3PerfectField
