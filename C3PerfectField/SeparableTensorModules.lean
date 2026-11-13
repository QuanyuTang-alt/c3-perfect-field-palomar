module

public import C3PerfectField.SeparableTensor
public import C3PerfectField.ScalarExtensionModules

/-!
The separable part of manuscript `lem:summand-descent`: extending a
restricted L-vector space along k contains its extension along L as a
retract. The inclusion uses the actual tensor idempotent for L ↪ K.
Compatibility with L-linear endomorphisms will supply the algebra action.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open scoped TensorProduct

universe u v w z

variable {k : Type u} {K : Type w} {L : Type v} {V : Type z}
  [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
  [Algebra L K] [IsScalarTower k L K]
  [AddCommGroup V] [Module k V] [Module L V] [IsScalarTower k L V]

/-- The tensor algebra K ⊗ L acts on K ⊗ V by the native L-action on V. -/
def tensorScalarRepresentation :
    (K ⊗[k] L) →ₐ[K] Module.End K (K ⊗[k] V) :=
  AlgHom.liftEquiv k K L _
    ((Module.End.baseChangeHom k K V).comp (Algebra.lsmul k k V))

omit [Algebra L K] [IsScalarTower k L K] in
theorem tensorScalarRepresentation_tmul (c d : K) (b : L) (n : V) :
    tensorScalarRepresentation (k := k) (K := K) (L := L) (V := V)
      (c ⊗ₜ[k] b) (d ⊗ₜ[k] n) = (c * d) ⊗ₜ[k] (b • n) := by
  change c • ((Algebra.lsmul k k V b).baseChange K) (d ⊗ₜ[k] n) = _
  rw [LinearMap.baseChange_tmul, Algebra.lsmul_apply, TensorProduct.smul_tmul']
  rfl

/-- The natural quotient that imposes the L-balancing relations. -/
def tensorRestrictionProjection : (K ⊗[k] V) →ₗ[K] (K ⊗[L] V) :=
  ((TensorProduct.mk L K V 1).restrictScalars k).liftBaseChange K

@[simp]
theorem tensorRestrictionProjection_tmul (c : K) (n : V) :
    tensorRestrictionProjection (k := k) (K := K) (L := L)
      (c ⊗ₜ[k] n) = c ⊗ₜ[L] n := by
  rw [tensorRestrictionProjection, LinearMap.liftBaseChange_tmul]
  simp only [LinearMap.restrictScalars_apply, TensorProduct.mk_apply,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The projection intertwines the tensor algebra action with evaluation. -/
theorem tensorRestrictionProjection_representation (s : K ⊗[k] L) (n : V) :
    tensorRestrictionProjection (k := k) (K := K) (L := L)
      (tensorScalarRepresentation (k := k) (K := K) (L := L) (V := V) s
        (1 ⊗ₜ[k] n)) =
      (AlgHom.liftEquiv k K L K (IsScalarTower.toAlgHom k L K) s) •
        (1 ⊗ₜ[L] n) := by
  induction s using TensorProduct.inductionOn with
  | tmul c b =>
    rw [tensorScalarRepresentation_tmul, mul_one, tensorRestrictionProjection_tmul,
      AlgHom.liftEquiv_tmul]
    simp only [smul_eq_mul, TensorProduct.smul_tmul', mul_one]
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
    rfl
  | add s t hs ht =>
    simp only [map_add, LinearMap.add_apply, hs, ht, add_smul]

variable {W : Type*} [AddCommGroup W] [Module k W] [Module L W]
  [IsScalarTower k L W]

omit [Algebra L K] [IsScalarTower k L K] in
/-- L-linear maps commute with the tensor L-action after extending along k. -/
theorem tensorScalarRepresentation_naturality (f : V →ₗ[L] W)
    (s : K ⊗[k] L) (x : K ⊗[k] V) :
    (f.restrictScalars k).baseChange K
        (tensorScalarRepresentation (k := k) (K := K) (L := L) (V := V) s x) =
      tensorScalarRepresentation (k := k) (K := K) (L := L) (V := W) s
        ((f.restrictScalars k).baseChange K x) := by
  induction s using TensorProduct.inductionOn with
  | tmul c b =>
    induction x using TensorProduct.inductionOn with
    | tmul d n =>
      simp only [tensorScalarRepresentation_tmul, LinearMap.baseChange_tmul,
        LinearMap.restrictScalars_apply, f.map_smul]
    | add x y hx hy => simp only [map_add, hx, hy]
  | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]

/-- The natural quotient also commutes with every L-linear map. -/
theorem tensorRestrictionProjection_naturality (f : V →ₗ[L] W) :
    f.baseChange K ∘ₗ tensorRestrictionProjection (k := k) (K := K) (L := L) =
      tensorRestrictionProjection (k := k) (K := K) (L := L) ∘ₗ
        (f.restrictScalars k).baseChange K := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c n
  simp only [LinearMap.comp_apply, tensorRestrictionProjection_tmul,
    LinearMap.baseChange_tmul, LinearMap.restrictScalars_apply]

variable [Module.Finite k L] [Algebra.IsSeparable k L] [IsSepClosed K]

/-- The L-linear map on tensor generators produced by the separable idempotent. -/
def separableTensorSectionGenerator : V →ₗ[L] (K ⊗[k] V) where
  toFun n := tensorScalarRepresentation (k := k) (K := K) (L := L) (V := V)
    (separableTensorIdempotent k K L (IsScalarTower.toAlgHom k L K)) (1 ⊗ₜ[k] n)
  map_add' n n' := by simp only [TensorProduct.tmul_add, map_add]
  map_smul' b n := by
    let ρ := tensorScalarRepresentation (k := k) (K := K) (L := L) (V := V)
    let s := separableTensorIdempotent k K L (IsScalarTower.toAlgHom k L K)
    change ρ s (1 ⊗ₜ[k] (b • n)) = b • ρ s (1 ⊗ₜ[k] n)
    have hin : ρ (1 ⊗ₜ[k] b) (1 ⊗ₜ[k] n) = 1 ⊗ₜ[k] (b • n) := by
      rw [tensorScalarRepresentation_tmul, one_mul]
    rw [← hin, ← Module.End.mul_apply, ← map_mul]
    rw [separableTensorIdempotent_mul_right, map_smul, LinearMap.smul_apply]
    exact IsScalarTower.algebraMap_smul (R := L) K b _

/-- The actual K-linear inclusion of the L-balanced tensor factor. -/
def separableTensorSection : (K ⊗[L] V) →ₗ[K] (K ⊗[k] V) :=
  (separableTensorSectionGenerator (k := k) (K := K) (L := L) (V := V)).liftBaseChange K

theorem separableTensorSection_tmul (c : K) (n : V) :
    separableTensorSection (k := k) (K := K) (L := L) (c ⊗ₜ[L] n) =
      c • tensorScalarRepresentation (k := k) (K := K) (L := L) (V := V)
        (separableTensorIdempotent k K L (IsScalarTower.toAlgHom k L K))
          (1 ⊗ₜ[k] n) := rfl

/-- The projection followed by the selected factor inclusion is the identity. -/
theorem tensorRestrictionProjection_comp_section :
    tensorRestrictionProjection (k := k) (K := K) (L := L) (V := V) ∘ₗ
        separableTensorSection (k := k) (K := K) (L := L) (V := V) =
      LinearMap.id := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c n
  simp only [LinearMap.comp_apply, separableTensorSection_tmul, map_smul,
    tensorRestrictionProjection_representation, separableTensorIdempotent_evaluation,
    one_smul, LinearMap.id_apply]
  simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- The separable inclusion commutes with every L-linear map. -/
theorem separableTensorSection_naturality (f : V →ₗ[L] W) :
    (f.restrictScalars k).baseChange K ∘ₗ
        separableTensorSection (k := k) (K := K) (L := L) =
      separableTensorSection (k := k) (K := K) (L := L) ∘ₗ f.baseChange K := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c n
  simp only [LinearMap.comp_apply, separableTensorSection_tmul, map_smul,
    tensorScalarRepresentation_naturality, LinearMap.baseChange_tmul,
    LinearMap.restrictScalars_apply]

end

end C3PerfectField
