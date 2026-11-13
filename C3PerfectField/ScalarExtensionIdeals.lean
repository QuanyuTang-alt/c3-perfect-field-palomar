module

public import C3PerfectField.ScalarExtensionGalois
public import C3PerfectField.Radicals
public import C3PerfectField.RadicalNilpotence
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
Manuscript `lem:jacobson-base` for finite-dimensional, possibly
noncommutative algebras. Tensor ideal nilpotence is proved explicitly;
no commutative ideal-map multiplication theorem is used.
-/

@[expose] public section

namespace C3PerfectField

noncomputable section

open scoped TensorProduct

universe u v w

variable {k : Type u} {K : Type w} {A : Type v}
  [Field k] [Field K] [Algebra k K] [Ring A] [Algebra k A]

/-- Left multiplication preserves the tensor extension of a left ideal. -/
theorem tensor_mul_mem_ideal_baseChange (I : Ideal A) (s z : K ⊗[k] A)
    (hz : z ∈ (I.restrictScalars k).baseChange K) :
    s * z ∈ (I.restrictScalars k).baseChange K := by
  rw [Submodule.baseChange_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, ha, rfl⟩ := hz
    induction s using TensorProduct.inductionOn with
    | tmul c b =>
      simpa only [TensorProduct.mk_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one] using
        (I.restrictScalars k).tmul_mem_baseChange_of_mem c (I.mul_mem_left b ha)
    | add s s' hs hs' =>
      simpa only [add_mul] using ((I.restrictScalars k).baseChange K).add_mem hs hs'
  | zero => simpa only [mul_zero] using ((I.restrictScalars k).baseChange K).zero_mem
  | add z z' _ _ hz hz' =>
    simpa only [mul_add] using ((I.restrictScalars k).baseChange K).add_mem hz hz'
  | smul c z _ hz =>
    simpa only [Algebra.mul_smul_comm] using
      ((I.restrictScalars k).baseChange K).smul_mem c hz

/-- The actual tensor subspace K ⊗ I, bundled as a left ideal of A_K. -/
def tensorExtendedIdeal (I : Ideal A) : Ideal (K ⊗[k] A) where
  carrier := (I.restrictScalars k).baseChange K
  zero_mem' := ((I.restrictScalars k).baseChange K).zero_mem
  add_mem' := ((I.restrictScalars k).baseChange K).add_mem
  smul_mem' s z hz := tensor_mul_mem_ideal_baseChange I s z hz

/-- Tensor extension preserves the right-ideal condition as well. -/
instance tensorExtendedIdeal_isTwoSided (I : Ideal A) [I.IsTwoSided] :
    (tensorExtendedIdeal (k := k) (K := K) I).IsTwoSided where
  mul_mem_of_left {z} s hz := by
    change z ∈ (I.restrictScalars k).baseChange K at hz
    change z * s ∈ (I.restrictScalars k).baseChange K
    rw [Submodule.baseChange_eq_span] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, rfl⟩ := hz
      induction s using TensorProduct.inductionOn with
      | tmul c b =>
        simpa only [TensorProduct.mk_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul] using
          (I.restrictScalars k).tmul_mem_baseChange_of_mem c (I.mul_mem_right b ha)
      | add s s' hs hs' =>
        simpa only [mul_add] using ((I.restrictScalars k).baseChange K).add_mem hs hs'
    | zero => simpa only [zero_mul] using ((I.restrictScalars k).baseChange K).zero_mem
    | add z z' _ _ hz hz' =>
      simpa only [add_mul] using ((I.restrictScalars k).baseChange K).add_mem hz hz'
    | smul c z _ hz =>
      simpa only [Algebra.smul_mul_assoc] using
        ((I.restrictScalars k).baseChange K).smul_mem c hz

@[simp]
theorem tensorExtendedIdeal_restrictScalars (I : Ideal A) :
    (tensorExtendedIdeal (k := k) (K := K) I).restrictScalars K =
      (I.restrictScalars k).baseChange K := by
  ext z
  rfl

@[simp]
theorem tensorExtendedIdeal_bot :
    tensorExtendedIdeal (k := k) (K := K) (⊥ : Ideal A) = ⊥ := by
  ext z
  simp [tensorExtendedIdeal]

@[simp]
theorem tensorExtendedIdeal_top :
    tensorExtendedIdeal (k := k) (K := K) (⊤ : Ideal A) = ⊤ := by
  ext z
  simp [tensorExtendedIdeal]

theorem tensorExtendedIdeal_mono {I J : Ideal A} (h : I ≤ J) :
    tensorExtendedIdeal (k := k) (K := K) I ≤ tensorExtendedIdeal J :=
  Submodule.baseChange_mono K h

/-- Multiplying extended ideals stays in the extension of their product.
This proof works for arbitrary left ideals in a noncommutative algebra. -/
theorem tensorExtendedIdeal_mul_le (I J : Ideal A) :
    tensorExtendedIdeal (k := k) (K := K) I * tensorExtendedIdeal J ≤
      tensorExtendedIdeal (I * J) := by
  apply Ideal.mul_le.mpr
  intro z hz w hw
  change z ∈ (I.restrictScalars k).baseChange K at hz
  change w ∈ (J.restrictScalars k).baseChange K at hw
  rw [Submodule.baseChange_eq_span] at hz hw
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, ha, rfl⟩ := hz
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨b, hb, rfl⟩ := hw
      change _ ∈ ((I * J).restrictScalars k).baseChange K
      simpa only [TensorProduct.mk_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul] using
        ((I * J).restrictScalars k).tmul_mem_baseChange_of_mem (1 : K)
          (Ideal.mul_mem_mul ha hb)
    | zero => simpa only [mul_zero] using (tensorExtendedIdeal (I * J)).zero_mem
    | add w w' _ _ hw hw' =>
      simpa only [mul_add] using (tensorExtendedIdeal (I * J)).add_mem hw hw'
    | smul c w _ hw =>
      change _ ∈ ((I * J).restrictScalars k).baseChange K at hw ⊢
      simpa only [Algebra.mul_smul_comm] using
        (((I * J).restrictScalars k).baseChange K).smul_mem c hw
  | zero => simpa only [zero_mul] using (tensorExtendedIdeal (I * J)).zero_mem
  | add z z' _ _ hz hz' =>
    simpa only [add_mul] using (tensorExtendedIdeal (I * J)).add_mem hz hz'
  | smul c z _ hz =>
    change _ ∈ ((I * J).restrictScalars k).baseChange K at hz ⊢
    simpa only [Algebra.smul_mul_assoc] using
      (((I * J).restrictScalars k).baseChange K).smul_mem c hz

/-- A single nilpotence exponent survives tensor extension. -/
theorem tensorExtendedIdeal_pow_le (I : Ideal A) (n : ℕ) :
    tensorExtendedIdeal (k := k) (K := K) I ^ n ≤ tensorExtendedIdeal (I ^ n) := by
  induction n with
  | zero => simp [Submodule.pow_zero]
  | succ n hn =>
    rw [Submodule.pow_succ, Submodule.pow_succ]
    exact (Ideal.mul_mono hn le_rfl).trans (tensorExtendedIdeal_mul_le _ _)

theorem tensorExtendedIdeal_isNilpotent (I : Ideal A) (hI : IsNilpotent I) :
    IsNilpotent (tensorExtendedIdeal (k := k) (K := K) I) := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  change I ^ n = ⊥ at hn
  change tensorExtendedIdeal I ^ n = ⊥
  exact eq_bot_iff.mpr ((tensorExtendedIdeal_pow_le I n).trans (by simp [hn]))

section RingFacts

variable {R : Type*} [Ring R]

theorem isNilpotent_of_mem_nilpotentIdeal (I : Ideal R) (hI : IsNilpotent I)
    {x : R} (hx : x ∈ I) : IsNilpotent x := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  change I ^ n = ⊥ at hn
  simpa only [hn, Ideal.mem_bot] using Ideal.pow_mem_pow hx n

/-- Nilpotent left ideals are contained in the Jacobson radical. -/
theorem nilpotentIdeal_le_jacobson (I : Ideal R) (hI : IsNilpotent I) :
    I ≤ Ideal.jacobson (⊥ : Ideal R) := by
  intro x hx
  rw [mem_jacobson_bot_iff_isUnit_one_sub_mul]
  intro y
  exact (isNilpotent_of_mem_nilpotentIdeal I hI (I.mul_mem_left y hx)).isUnit_one_sub

/-- Ring automorphisms preserve the radical, also for noncommutative R. -/
theorem ringEquiv_mem_jacobson {S : Type*} [Ring S] (e : R ≃+* S) {x : R}
    (hx : x ∈ Ideal.jacobson (⊥ : Ideal R)) :
    e x ∈ Ideal.jacobson (⊥ : Ideal S) := by
  rw [mem_jacobson_bot_iff_isUnit_one_sub_mul] at hx ⊢
  intro y
  simpa only [map_sub, map_one, map_mul, e.apply_symm_apply] using
    (hx (e.symm y)).map e

/-- A ring equivalence identifies both Jacobson radicals. -/
theorem ringEquiv_mem_jacobson_iff {S : Type*} [Ring S] (e : R ≃+* S) (x : R) :
    e x ∈ Ideal.jacobson (⊥ : Ideal S) ↔ x ∈ Ideal.jacobson (⊥ : Ideal R) := by
  constructor
  · intro hx
    simpa only [e.symm_apply_apply] using ringEquiv_mem_jacobson e.symm hx
  · exact ringEquiv_mem_jacobson e

end RingFacts

variable [Module.Finite k A]

/-- One inclusion holds for every field extension: extend the nilpotent
radical ideal, then apply the noncommutative Jacobson criterion. -/
theorem tensorExtendedIdeal_jacobson_le :
    tensorExtendedIdeal (k := k) (K := K) (Ideal.jacobson (⊥ : Ideal A)) ≤
      Ideal.jacobson (⊥ : Ideal (K ⊗[k] A)) :=
  nilpotentIdeal_le_jacobson _
    (tensorExtendedIdeal_isNilpotent _ (jacobson_isNilpotent k A))

/-- The ideal obtained by pulling the extended radical back along
the canonical inclusion is contained in the original radical. -/
theorem comap_tensor_jacobson_le :
    Ideal.comap (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A)
      (Ideal.jacobson (⊥ : Ideal (K ⊗[k] A))) ≤ Ideal.jacobson (⊥ : Ideal A) := by
  let J := Ideal.jacobson (⊥ : Ideal (K ⊗[k] A))
  let f : A →ₐ[k] K ⊗[k] A := Algebra.TensorProduct.includeRight
  intro a ha
  rw [mem_jacobson_bot_iff_isUnit_one_sub_mul]
  intro b
  have hba : f (b * a) ∈ J := by
    rw [map_mul]
    exact J.mul_mem_left (f b) ha
  have hn := isNilpotent_of_mem_nilpotentIdeal J (jacobson_isNilpotent K (K ⊗[k] A)) hba
  have hf : Function.Injective f :=
    scalarTensorInclusion_injective (k := k) (K := K)
  exact ((IsNilpotent.map_iff hf).mp hn).isUnit_one_sub

/-- Pullback of the extended radical recovers the original radical even
without a fixed-field or perfection assumption. -/
theorem comap_tensor_jacobson :
    Ideal.comap (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A)
      (Ideal.jacobson (⊥ : Ideal (K ⊗[k] A))) = Ideal.jacobson (⊥ : Ideal A) := by
  apply le_antisymm comap_tensor_jacobson_le
  intro a ha
  apply tensorExtendedIdeal_jacobson_le
  exact ((Ideal.jacobson (⊥ : Ideal A)).restrictScalars k).tmul_mem_baseChange_of_mem 1 ha

/-- Manuscript `lem:jacobson-base`, with exactly the fixed-scalar hypothesis.
The tensor subspace descent identifies the actual radical ideal. -/
theorem jacobson_scalarExtension (G : Subgroup (K ≃ₐ[k] K))
    (hG : ∀ x : K, (∀ σ : G, σ.val x = x) → ∃ c : k, algebraMap k K c = x) :
    Ideal.jacobson (⊥ : Ideal (K ⊗[k] A)) =
      tensorExtendedIdeal (k := k) (K := K) (Ideal.jacobson (⊥ : Ideal A)) := by
  let J := Ideal.jacobson (⊥ : Ideal (K ⊗[k] A))
  let W := J.restrictScalars K
  let I := Ideal.comap (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) J
  have hW : ∀ (σ : G) (z : K ⊗[k] A), z ∈ W → tensorGaloisAction σ.val z ∈ W := by
    intro σ z hz
    change tensorGaloisAction σ.val z ∈ J
    rw [← scalarExtensionAlgebraAut_eq_tensorGaloisAction]
    exact ringEquiv_mem_jacobson (scalarExtensionAlgebraAut σ.val).toRingEquiv hz
  have hI : descendedTensorSubspace W = I.restrictScalars k := by
    ext a
    rfl
  have hdesc : J = tensorExtendedIdeal (k := k) (K := K) I := by
    ext z
    change z ∈ W ↔ z ∈ (I.restrictScalars k).baseChange K
    rw [tensor_subspace_descent G hG W hW, hI]
  apply le_antisymm
  · change J ≤ tensorExtendedIdeal (k := k) (K := K) (Ideal.jacobson (⊥ : Ideal A))
    rw [hdesc]
    exact tensorExtendedIdeal_mono comap_tensor_jacobson_le
  · exact tensorExtendedIdeal_jacobson_le

/-- The literal fixed-field condition in the manuscript suffices. -/
theorem jacobson_scalarExtension_of_fixedField (G : Subgroup (K ≃ₐ[k] K))
    (hG : IntermediateField.fixedField G = ⊥) :
    Ideal.jacobson (⊥ : Ideal (K ⊗[k] A)) =
      tensorExtendedIdeal (k := k) (K := K) (Ideal.jacobson (⊥ : Ideal A)) :=
  jacobson_scalarExtension G (fun x hx =>
    (subgroup_fixed_iff G hG x).mp hx)

/-- Perfection discharges the fixed-field input for an algebraic closure. -/
theorem algebraicClosure_jacobson_scalarExtension [PerfectField k] [IsAlgClosure k K] :
    Ideal.jacobson (⊥ : Ideal (K ⊗[k] A)) =
      tensorExtendedIdeal (k := k) (K := K) (Ideal.jacobson (⊥ : Ideal A)) :=
  jacobson_scalarExtension_of_fixedField _ algebraicClosure_fixedField

end

end C3PerfectField
