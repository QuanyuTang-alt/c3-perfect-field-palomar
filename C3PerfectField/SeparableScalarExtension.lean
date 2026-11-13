module

public import C3PerfectField.SeparableTensorModules

/-!
The separable tensor retraction is upgraded to actual A_K-module maps.
M carries an L-vector-space structure commuting with its A-action, as
does the restriction of any A_L-module. No module-descent assertion is
assumed: the finite field of definition remains a separate obligation.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open CategoryTheory
open scoped ModuleCat TensorProduct

universe u v

variable {k K L : Type u} {A : Type v}
  [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
  [Algebra L K] [IsScalarTower k L K] [Ring A] [Algebra k A]
  (M : ModuleCat.{max u v} A) [Module L M] [IsScalarTower k L M]
  [SMulCommClass A L M]

/-- The A_K-action on K ⊗_L M obtained by extending the commuting A-action. -/
def relativeScalarExtensionRepresentation :
    (K ⊗[k] A) →ₐ[K] Module.End K (K ⊗[L] M) :=
  AlgHom.liftEquiv k K A _
    (((Module.End.baseChangeHom L K M).restrictScalars k).comp (Algebra.lsmul k L M))

theorem relativeScalarExtensionRepresentation_tmul (c d : K) (a : A) (n : M) :
    relativeScalarExtensionRepresentation (k := k) (K := K) (L := L) M
      (c ⊗ₜ[k] a) (d ⊗ₜ[L] n) = (c * d) ⊗ₜ[L] (a • n) := by
  change c • ((Algebra.lsmul k L M a).baseChange K) (d ⊗ₜ[L] n) = _
  rw [LinearMap.baseChange_tmul, Algebra.lsmul_apply, TensorProduct.smul_tmul']
  rfl

/-- K ⊗_L M as a module over the original extended algebra K ⊗_k A. -/
def relativeScalarExtensionObject : ModuleCat.{max u v} (K ⊗[k] A) :=
  letI := Module.compHom (K ⊗[L] M)
    (relativeScalarExtensionRepresentation (k := k) (K := K) (L := L) M).toRingHom
  ModuleCat.of (K ⊗[k] A) (K ⊗[L] M)

/-- Projection respects the full extended algebra action. -/
theorem tensorRestrictionProjection_algebraAction (s : K ⊗[k] A) (z : K ⊗[k] M) :
    tensorRestrictionProjection (k := k) (K := K) (L := L)
        (scalarExtensionRepresentation (k := k) (K := K) M s z) =
      relativeScalarExtensionRepresentation (k := k) (K := K) (L := L) M s
        (tensorRestrictionProjection (k := k) (K := K) (L := L) z) := by
  induction s using TensorProduct.inductionOn with
  | tmul c a =>
    let f := Algebra.lsmul k L M a
    change tensorRestrictionProjection (k := k) (K := K) (L := L)
      (c • (f.restrictScalars k).baseChange K z) =
        c • f.baseChange K (tensorRestrictionProjection (k := k) (K := K) (L := L) z)
    rw [map_smul]
    congr 1
    exact (LinearMap.congr_fun (tensorRestrictionProjection_naturality f) z).symm
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]

/-- The natural projection as an actual A_K-module morphism. -/
def separableScalarExtensionProjection :
    scalarExtensionObject (k := k) (K := K) M ⟶
      relativeScalarExtensionObject (k := k) (K := K) (L := L) M := by
  letI := Module.compHom (K ⊗[k] M)
    (scalarExtensionRepresentation (k := k) (K := K) M).toRingHom
  letI := Module.compHom (K ⊗[L] M)
    (relativeScalarExtensionRepresentation (k := k) (K := K) (L := L) M).toRingHom
  exact ModuleCat.ofHom {
    toAddHom := (tensorRestrictionProjection (k := k) (K := K) (L := L) (V := M)).toAddHom
    map_smul' := tensorRestrictionProjection_algebraAction M
  }

variable [Module.Finite k L] [Algebra.IsSeparable k L] [IsSepClosed K]

/-- The separable factor inclusion respects the full extended algebra action. -/
theorem separableTensorSection_algebraAction (s : K ⊗[k] A) (z : K ⊗[L] M) :
    separableTensorSection (k := k) (K := K) (L := L)
        (relativeScalarExtensionRepresentation (k := k) (K := K) (L := L) M s z) =
      scalarExtensionRepresentation (k := k) (K := K) M s
        (separableTensorSection (k := k) (K := K) (L := L) z) := by
  induction s using TensorProduct.inductionOn with
  | tmul c a =>
    let f := Algebra.lsmul k L M a
    change separableTensorSection (k := k) (K := K) (L := L)
      (c • f.baseChange K z) =
        c • (f.restrictScalars k).baseChange K
          (separableTensorSection (k := k) (K := K) (L := L) z)
    rw [map_smul]
    congr 1
    exact (LinearMap.congr_fun (separableTensorSection_naturality f) z).symm
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]

/-- The selected separable factor as an actual A_K-module morphism. -/
def separableScalarExtensionSection :
    relativeScalarExtensionObject (k := k) (K := K) (L := L) M ⟶
      scalarExtensionObject (k := k) (K := K) M := by
  letI := Module.compHom (K ⊗[k] M)
    (scalarExtensionRepresentation (k := k) (K := K) M).toRingHom
  letI := Module.compHom (K ⊗[L] M)
    (relativeScalarExtensionRepresentation (k := k) (K := K) (L := L) M).toRingHom
  exact ModuleCat.ofHom {
    toAddHom := (separableTensorSection (k := k) (K := K) (L := L) (V := M)).toAddHom
    map_smul' := separableTensorSection_algebraAction M
  }

/-- The splitting equation in the actual module category. -/
theorem separableScalarExtension_section_projection :
    separableScalarExtensionSection (k := k) (K := K) (L := L) M ≫
        separableScalarExtensionProjection (k := k) (K := K) (L := L) M =
      𝟙 (relativeScalarExtensionObject (k := k) (K := K) (L := L) M) := by
  ext z
  exact LinearMap.congr_fun
    (tensorRestrictionProjection_comp_section (k := k) (K := K) (L := L) (V := M)) z

/-- The separable summand step, with actual A_K objects and splitting maps. -/
def relativeScalarExtension_retract :
    Retract (relativeScalarExtensionObject (k := k) (K := K) (L := L) M)
      (scalarExtensionObject (k := k) (K := K) M) :=
  ⟨separableScalarExtensionSection M, separableScalarExtensionProjection M,
    separableScalarExtension_section_projection M⟩

end

end C3PerfectField
