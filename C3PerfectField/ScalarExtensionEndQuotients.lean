-- Ported for the pinned Lean/Mathlib version with Doubao assistance; original notices retained.
module

public import C3PerfectField.ScalarExtensionFixedTwists
public import C3PerfectField.ScalarExtensionRadicals
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
The semisimple endomorphism quotient in manuscript `lem:transitivity`.
Scalar extension of a two-sided ideal quotient works here for
noncommutative algebras. The resulting canonical endomorphism-quotient
equivalence uses the already proved Jacobson base-change equality.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open CategoryTheory
open scoped ModuleCat TensorProduct

universe u v w

section Ideals

variable {k : Type u} {K : Type w} {A : Type v}
  [Field k] [Field K] [Algebra k K] [Ring A] [Algebra k A]

/-- The canonical tensor-quotient equivalence for a possibly noncommutative
algebra and a two-sided ideal. -/
def tensorExtendedIdealQuotientAlgEquiv (I : Ideal A) [I.IsTwoSided] :
    ((K ⊗[k] A) ⧸ tensorExtendedIdeal (k := k) (K := K) I) ≃ₐ[K]
      K ⊗[k] (A ⧸ I) := by
  let e :
      ((K ⊗[k] A) ⧸ tensorExtendedIdeal (k := k) (K := K) I) ≃ₗ[K]
        K ⊗[k] (A ⧸ I) :=
    scalarExtensionQuotientEquiv (I.restrictScalars k)
  have he (c : K) (a : A) :
      e (Ideal.Quotient.mk _ (c ⊗ₜ[k] a)) = c ⊗ₜ[k] Ideal.Quotient.mk I a :=
    scalarExtensionQuotientEquiv_mk (I.restrictScalars k) c a
  refine AlgEquiv.ofLinearEquiv e ?_ ?_
  · change e (Ideal.Quotient.mk _ ((1 : K) ⊗ₜ[k] (1 : A))) = _
    rw [he]
    rfl
  · intro x y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul]
    induction s using TensorProduct.inductionOn with
    | tmul c a =>
      induction t using TensorProduct.inductionOn with
      | tmul d b =>
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        rw [he, he, he, Algebra.TensorProduct.tmul_mul_tmul]
        rfl
      | add t t' ht ht' =>
        simpa only [mul_add, map_add] using congrArg₂ (· + ·) ht ht'
    | add s s' hs hs' =>
      simpa only [add_mul, map_add] using congrArg₂ (· + ·) hs hs'

set_option maxHeartbeats 800000 in
/-- The algebra equivalence is induced by the ordinary quotient map. -/
theorem tensorExtendedIdealQuotientAlgEquiv_mk_tmul
    (I : Ideal A) [I.IsTwoSided] (c : K) (a : A) :
    tensorExtendedIdealQuotientAlgEquiv (K := K) I
        (Ideal.Quotient.mk _ (c ⊗ₜ[k] a)) =
      c ⊗ₜ[k] Ideal.Quotient.mk I a := by
  unfold tensorExtendedIdealQuotientAlgEquiv
  exact scalarExtensionQuotientEquiv_mk (I.restrictScalars k) c a

/-- Ring equivalences transport the actual Jacobson ideal. -/
theorem jacobson_eq_map_ringEquiv {R S : Type*} [Ring R] [Ring S]
    (e : R ≃+* S) :
    Ideal.jacobson (⊥ : Ideal S) =
      (Ideal.jacobson (⊥ : Ideal R)).map e := by
  apply le_antisymm
  · intro y hy
    have hx : e.symm y ∈ Ideal.jacobson (⊥ : Ideal R) :=
      (ringEquiv_mem_jacobson_iff e _).mp (by simpa using hy)
    simpa only [e.apply_symm_apply] using Ideal.mem_map_of_mem e hx
  · exact Ideal.map_le_iff_le_comap.mpr fun x hx => ringEquiv_mem_jacobson e hx

variable [Module.Finite k A] [PerfectField k] [IsAlgClosure k K]

/-- The semisimple quotient of an extended algebra is the extension of its
semisimple quotient, with no extra semisimplicity premise. -/
def jacobsonQuotientScalarExtensionAlgEquiv :
    ((K ⊗[k] A) ⧸ Ideal.jacobson (⊥ : Ideal (K ⊗[k] A))) ≃ₐ[K]
      K ⊗[k] (A ⧸ Ideal.jacobson (⊥ : Ideal A)) :=
  (Ideal.quotientEquivAlgOfEq K
    (algebraicClosure_jacobson_scalarExtension (k := k) (K := K) (A := A))).trans
      (tensorExtendedIdealQuotientAlgEquiv _)

theorem jacobsonQuotientScalarExtensionAlgEquiv_mk_tmul (c : K) (a : A) :
    jacobsonQuotientScalarExtensionAlgEquiv (k := k) (K := K) (A := A)
        (Ideal.Quotient.mk _ (c ⊗ₜ[k] a)) =
      c ⊗ₜ[k] Ideal.Quotient.mk (Ideal.jacobson (⊥ : Ideal A)) a := by
  rw [jacobsonQuotientScalarExtensionAlgEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlgOfEq_mk, tensorExtendedIdealQuotientAlgEquiv_mk_tmul]

/-- Coefficient Galois action descends to the actual Jacobson quotient. -/
def jacobsonQuotientGaloisAut (σ : K ≃ₐ[k] K) :
    ((K ⊗[k] A) ⧸ Ideal.jacobson (⊥ : Ideal (K ⊗[k] A))) ≃ₐ[k]
      ((K ⊗[k] A) ⧸ Ideal.jacobson (⊥ : Ideal (K ⊗[k] A))) :=
  Ideal.quotientEquivAlg _ _ (scalarExtensionAlgebraAut σ)
    (jacobson_eq_map_ringEquiv (scalarExtensionAlgebraAut σ).toRingEquiv)

omit [Module.Finite k A] [PerfectField k] [IsAlgClosure k K] in
theorem jacobsonQuotientGaloisAut_mk (σ : K ≃ₐ[k] K) (z : K ⊗[k] A) :
    jacobsonQuotientGaloisAut σ (Ideal.Quotient.mk _ z) =
      Ideal.Quotient.mk _ (scalarExtensionAlgebraAut σ z) := rfl

/-- The canonical semisimple quotient equivalence is Galois equivariant,
rather than merely an abstract algebra equivalence. -/
theorem jacobsonQuotientScalarExtensionAlgEquiv_galois (σ : K ≃ₐ[k] K)
    (z : (K ⊗[k] A) ⧸ Ideal.jacobson (⊥ : Ideal (K ⊗[k] A))) :
    jacobsonQuotientScalarExtensionAlgEquiv (k := k) (K := K) (A := A)
        (jacobsonQuotientGaloisAut σ z) =
      tensorGaloisAction σ
        (jacobsonQuotientScalarExtensionAlgEquiv (k := k) (K := K) (A := A) z) := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [jacobsonQuotientGaloisAut_mk]
  induction z using TensorProduct.inductionOn with
  | tmul c a =>
    rw [scalarExtensionAlgebraAut_tmul,
      jacobsonQuotientScalarExtensionAlgEquiv_mk_tmul,
      jacobsonQuotientScalarExtensionAlgEquiv_mk_tmul,
      tensorGaloisAction_tmul]
  | add z z' hz hz' =>
    simpa only [map_add] using congrArg₂ (· + ·) hz hz'

end Ideals

section EndModules

variable {k K : Type u} {A : Type v}
  [Field k] [Field K] [Algebra k K] [Ring A] [Algebra k A]
  [Module.Finite k A] [PerfectField k] [IsAlgClosure k K]
  (M : ModuleCat.{max u v} A) [Module.Finite k M]

/-- The actual endomorphism quotient in the manuscript, with the canonical
Hom equivalence and Jacobson equality used to identify both quotients. -/
def moduleEndJacobsonQuotientScalarExtensionAlgEquiv :
    (End (scalarExtensionObject (k := k) (K := K) M) ⧸
      Ideal.jacobson (⊥ : Ideal
        (End (scalarExtensionObject (k := k) (K := K) M)))) ≃ₐ[K]
      K ⊗[k] (End M ⧸ Ideal.jacobson (⊥ : Ideal (End M))) := by
  let := finite_module_end (k := k) M
  let e := moduleEndScalarExtensionAlgEquiv (k := k) (K := K) M
  exact (Ideal.quotientEquivAlg _ _ e.symm
    (jacobson_eq_map_ringEquiv e.symm.toRingEquiv)).trans
      jacobsonQuotientScalarExtensionAlgEquiv

/-- The endomorphism-quotient map sends the actual extension of c ⊗ f to
c ⊗ [f], so it is the identification used in `lem:transitivity`. -/
theorem moduleEndJacobsonQuotientScalarExtensionAlgEquiv_mk_tmul
    (c : K) (f : End M) :
    moduleEndJacobsonQuotientScalarExtensionAlgEquiv (K := K) M
        (Ideal.Quotient.mk _
          (moduleEndScalarExtensionAlgEquiv (K := K) M (c ⊗ₜ[k] f))) =
      c ⊗ₜ[k] Ideal.Quotient.mk (Ideal.jacobson (⊥ : Ideal (End M))) f := by
  let := finite_module_end (k := k) M
  rw [moduleEndJacobsonQuotientScalarExtensionAlgEquiv, AlgEquiv.trans_apply,
    Ideal.quotientEquivAlg_mk, AlgEquiv.symm_apply_apply,
    jacobsonQuotientScalarExtensionAlgEquiv_mk_tmul]

end EndModules

section EndGalois

variable {k K : Type u} {A : Type v}
  [Field k] [Field K] [Algebra k K] [Ring A] [Algebra k A]
  [Module.Finite k A] (M : ModuleCat.{max u v} A) [Module.Finite k M]

/-- The two field actions on extended endomorphisms are the canonical
restrictions of the same extended-algebra module action. -/
instance moduleEndScalarExtensionTower :
    IsScalarTower k K (End (scalarExtensionObject (k := k) (K := K) M)) :=
  IsScalarTower.of_algebraMap_smul fun c f => by
    apply End.homEquiv.injective
    ext x
    change algebraMap K (K ⊗[k] A) (algebraMap k K c) • f.asHom x =
      algebraMap k (K ⊗[k] A) c • f.asHom x
    rw [← IsScalarTower.algebraMap_apply k K (K ⊗[k] A)]

/-- Coefficient action on the actual extended endomorphism algebra, using
the canonical scalar-extension identification. -/
def moduleEndGaloisAut (σ : K ≃ₐ[k] K) :
    End (scalarExtensionObject (k := k) (K := K) M) ≃ₐ[k]
      End (scalarExtensionObject (k := k) (K := K) M) :=
  ((moduleEndScalarExtensionAlgEquiv (k := k) (K := K) M).symm.restrictScalars k).trans
    ((scalarExtensionAlgebraAut (A := End M) σ).trans
      ((moduleEndScalarExtensionAlgEquiv (k := k) (K := K) M).restrictScalars k))

theorem moduleEndGaloisAut_scalarExtension (σ : K ≃ₐ[k] K)
    (z : K ⊗[k] End M) :
    moduleEndGaloisAut M σ (moduleEndScalarExtensionAlgEquiv M z) =
      moduleEndScalarExtensionAlgEquiv M (tensorGaloisAction σ z) := by
  simp only [moduleEndGaloisAut, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    AlgEquiv.symm_apply_apply, scalarExtensionAlgebraAut_eq_tensorGaloisAction]

/-- The coefficient action is exactly conjugation by the fixed-twist
isomorphism on the actual endomorphisms. -/
theorem moduleEndGaloisAut_eq_twistConjugate (σ : K ≃ₐ[k] K)
    (f : End (scalarExtensionObject (k := k) (K := K) M)) :
    moduleEndGaloisAut M σ f = End.of (scalarExtensionTwistConjugate σ f.asHom) := by
  obtain ⟨z, rfl⟩ := (moduleEndScalarExtensionAlgEquiv (k := k) (K := K) M).surjective f
  rw [moduleEndGaloisAut_scalarExtension]
  have hAdd (f g : End (scalarExtensionObject (k := k) (K := K) M)) :
      scalarExtensionTwistConjugate σ (f + g).asHom =
        scalarExtensionTwistConjugate σ f.asHom +
          scalarExtensionTwistConjugate σ g.asHom := by
    change scalarExtensionTwistConjugate σ (f.asHom + g.asHom) = _
    simp only [scalarExtensionTwistConjugate, Functor.map_add,
      Preadditive.comp_add, Preadditive.add_comp]
  induction z using TensorProduct.inductionOn with
  | tmul c f =>
    apply End.homEquiv.injective
    change moduleHomScalarExtensionEquiv M M (σ c ⊗ₜ[k] f.asHom) =
      scalarExtensionTwistConjugate σ
        (moduleHomScalarExtensionEquiv M M (c ⊗ₜ[k] f.asHom))
    exact (scalarExtensionTwistConjugate_tmul σ M M c f.asHom).symm
  | add z z' hz hz' =>
    simp only [map_add]
    rw [hAdd, hz, hz']

variable [PerfectField k] [IsAlgClosure k K]

/-- Twisting acts on the actual semisimple endomorphism quotient. -/
def moduleEndJacobsonQuotientGaloisAut (σ : K ≃ₐ[k] K) :
    (End (scalarExtensionObject (k := k) (K := K) M) ⧸
      Ideal.jacobson (⊥ : Ideal
        (End (scalarExtensionObject (k := k) (K := K) M)))) ≃ₐ[k]
      (End (scalarExtensionObject (k := k) (K := K) M) ⧸
        Ideal.jacobson (⊥ : Ideal
          (End (scalarExtensionObject (k := k) (K := K) M)))) :=
  Ideal.quotientEquivAlg _ _ (moduleEndGaloisAut M σ)
    (jacobson_eq_map_ringEquiv (moduleEndGaloisAut M σ).toRingEquiv)

omit [PerfectField k] [IsAlgClosure k K] in
theorem moduleEndJacobsonQuotientGaloisAut_mk (σ : K ≃ₐ[k] K)
    (f : End (scalarExtensionObject (k := k) (K := K) M)) :
    moduleEndJacobsonQuotientGaloisAut M σ (Ideal.Quotient.mk _ f) =
      Ideal.Quotient.mk _ (moduleEndGaloisAut M σ f) := rfl

/-- Equivariance of the exact endomorphism-quotient identification used in
the manuscript's transitivity proof. -/
theorem moduleEndJacobsonQuotientScalarExtensionAlgEquiv_galois
    (σ : K ≃ₐ[k] K)
    (z : End (scalarExtensionObject (k := k) (K := K) M) ⧸
      Ideal.jacobson (⊥ : Ideal
        (End (scalarExtensionObject (k := k) (K := K) M)))) :
    moduleEndJacobsonQuotientScalarExtensionAlgEquiv (K := K) M
        (moduleEndJacobsonQuotientGaloisAut M σ z) =
      tensorGaloisAction σ
        (moduleEndJacobsonQuotientScalarExtensionAlgEquiv (K := K) M z) := by
  let := finite_module_end (k := k) M
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨z, rfl⟩ := (moduleEndScalarExtensionAlgEquiv (k := k) (K := K) M).surjective f
  rw [moduleEndJacobsonQuotientGaloisAut_mk, moduleEndGaloisAut_scalarExtension]
  induction z using TensorProduct.inductionOn with
  | tmul c f =>
    rw [tensorGaloisAction_tmul,
      moduleEndJacobsonQuotientScalarExtensionAlgEquiv_mk_tmul,
      moduleEndJacobsonQuotientScalarExtensionAlgEquiv_mk_tmul,
      tensorGaloisAction_tmul]
  | add z z' hz hz' =>
    simpa only [map_add] using congrArg₂ (· + ·) hz hz'

end EndGalois

section FixedIdempotents

variable {k : Type u} {K : Type w} {R : Type v}
  [Field k] [Field K] [Algebra k K] [Ring R] [Algebra k R]

/-- A possibly noncommutative local ring has only two idempotents. -/
theorem isIdempotentElem_eq_zero_or_one_of_local [IsLocalRing R]
    {e : R} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · exact Or.inr ((IsIdempotentElem.iff_eq_one_of_isUnit h).mp he)
  · exact Or.inl (by
      have h' := (IsIdempotentElem.iff_eq_one_of_isUnit h).mp he.one_sub
      exact sub_eq_self.mp h')

/-- The radical quotient of a noncommutative local ring remains local. -/
theorem isLocalRing_jacobsonQuotient [IsLocalRing R] :
    IsLocalRing (R ⧸ Ideal.jacobson (⊥ : Ideal R)) := by
  let : Nontrivial (R ⧸ Ideal.jacobson (⊥ : Ideal R)) :=
    Ideal.Quotient.nontrivial_iff.mpr (by
      exact fun h => (bot_ne_top : (⊥ : Ideal R) ≠ ⊤)
        (Ideal.jacobson_eq_top_iff.mp h))
  exact IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

variable [Module.Finite k R] [PerfectField k] [IsAlgClosure k K]

/-- The invariant-idempotent contradiction in the transitivity proof.
Descent and faithful tensor inclusion discharge the Galois and idempotent
steps; the original algebra is allowed to be noncommutative. -/
theorem algebraicClosure_tensor_fixed_idempotent_eq_zero_or_one
    [IsLocalRing R] {e : K ⊗[k] R}
    (he : IsIdempotentElem e)
    (hfix : ∀ σ : K ≃ₐ[k] K, tensorGaloisAction σ e = e) :
    e = 0 ∨ e = 1 := by
  obtain ⟨d, rfl⟩ := (algebraicClosure_tensor_fixed_iff e).mp hfix
  have hd : IsIdempotentElem d := by
    change d * d = d
    apply scalarTensorInclusion_injective (k := k) (K := K)
    change (1 : K) ⊗ₜ[k] (d * d) = 1 ⊗ₜ[k] d
    simpa only [IsIdempotentElem, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul] using he
  rcases isIdempotentElem_eq_zero_or_one_of_local hd with rfl | rfl
  · exact Or.inl (TensorProduct.tmul_zero _ _)
  · exact Or.inr rfl

end FixedIdempotents

section Indecomposables

variable {k K : Type u} {A : Type v}
  [Field k] [Field K] [Algebra k K] [Ring A] [Algebra k A]
  [Module.Finite k A] [PerfectField k] [IsAlgClosure k K]
  (X : IndecomposableModule k A)

/-- In the semisimple endomorphism quotient of an extended indecomposable,
every idempotent fixed by coefficient Galois action is 0 or 1.
This conclusion uses the actual original indecomposable module. -/
theorem moduleEndJacobsonQuotient_fixed_idempotent_eq_zero_or_one
    {e : End (scalarExtensionObject (k := k) (K := K) X.obj) ⧸
      Ideal.jacobson (⊥ : Ideal
        (End (scalarExtensionObject (k := k) (K := K) X.obj)))}
    (he : IsIdempotentElem e)
    (hfix : letI : Module.Finite k X.obj := X.val.property
      ∀ σ : K ≃ₐ[k] K,
      tensorGaloisAction σ
        (moduleEndJacobsonQuotientScalarExtensionAlgEquiv (K := K) X.obj e) =
      moduleEndJacobsonQuotientScalarExtensionAlgEquiv (K := K) X.obj e) :
    e = 0 ∨ e = 1 := by
  let := X.val.property
  let := finite_module_end (k := k) X.obj
  let := isLocalRing_end_of_finite_indecomposable X
  let := isLocalRing_jacobsonQuotient (R := End X.obj)
  let d := moduleEndJacobsonQuotientScalarExtensionAlgEquiv (k := k) (K := K) X.obj
  have hd : IsIdempotentElem (d e) := by
    simpa only [IsIdempotentElem, map_mul] using congrArg d he
  rcases algebraicClosure_tensor_fixed_idempotent_eq_zero_or_one hd hfix with h | h
  · exact Or.inl (d.injective (by simpa only [map_zero] using h))
  · exact Or.inr (d.injective (by simpa only [map_one] using h))

/-- The same invariant-idempotent conclusion expressed by the actual
quotient automorphisms induced by twisting. -/
theorem moduleEndJacobsonQuotient_twist_fixed_idempotent_eq_zero_or_one
    {e : End (scalarExtensionObject (k := k) (K := K) X.obj) ⧸
      Ideal.jacobson (⊥ : Ideal
        (End (scalarExtensionObject (k := k) (K := K) X.obj)))}
    (he : IsIdempotentElem e)
    (hfix : letI : Module.Finite k X.obj := X.val.property
      ∀ σ : K ≃ₐ[k] K,
        moduleEndJacobsonQuotientGaloisAut X.obj σ e = e) :
    e = 0 ∨ e = 1 := by
  let := X.val.property
  apply moduleEndJacobsonQuotient_fixed_idempotent_eq_zero_or_one X he
  intro σ
  rw [← moduleEndJacobsonQuotientScalarExtensionAlgEquiv_galois, hfix σ]

end Indecomposables

end

end C3PerfectField
