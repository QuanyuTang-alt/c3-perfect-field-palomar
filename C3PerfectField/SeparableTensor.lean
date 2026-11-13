module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
Manuscript `lem:separable-tensor`. The étale splitting is reindexed by
the actual k-algebra embeddings L → K, and its coordinates are proved
to be the tensor evaluations from the manuscript.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open scoped TensorProduct Classical

universe u v w

section SplitAlgebra

variable {K : Type w} {B : Type v} [Field K] [CommRing B] [Algebra K B]
  [Algebra.EssFiniteType K B] [Algebra.FormallyEtale K B] [IsSepClosed K]

/-- A coordinate in the étale splitting, regarded as an actual algebra map. -/
def splitAlgebraCoordinate (p : PrimeSpectrum B) : B →ₐ[K] K :=
  (Pi.evalAlgHom K (fun _ : PrimeSpectrum B => K) p).comp
    (Algebra.FormallyEtale.equivPiOfIsSepClosed K B).toAlgHom

@[simp]
theorem splitAlgebraCoordinate_apply (p : PrimeSpectrum B) (x : B) :
    splitAlgebraCoordinate (K := K) p x =
      Algebra.FormallyEtale.equivPiOfIsSepClosed K B x p := rfl

/-- Every K-point is evaluation at the inverse image of the zero prime. -/
theorem splitAlgebraCoordinate_comap (f : B →ₐ[K] K) :
    splitAlgebraCoordinate (K := K)
      ((⟨⊥, inferInstance⟩ : PrimeSpectrum K).comap f) = f := by
  ext x
  exact (Algebra.FormallyEtale.equivPiOfIsSepClosed_comap f x _).trans
    (Algebra.FormallyEtale.equivPiOfIsSepClosed_self_apply (f x) _)

/-- The prime coordinates of a split étale algebra are its actual K-points. -/
def splitAlgebraPointEquiv : PrimeSpectrum B ≃ (B →ₐ[K] K) :=
  Equiv.ofBijective (splitAlgebraCoordinate (K := K)) (by
    classical
    constructor
    · intro p q hpq
      by_contra hne
      let e := Algebra.FormallyEtale.equivPiOfIsSepClosed K B
      have h := DFunLike.congr_fun hpq (e.symm (Pi.single p 1))
      have hp : e (e.symm (Pi.single p 1)) p = 1 := by simp
      have hq : e (e.symm (Pi.single p 1)) q = 0 := by
        simp [Ne.symm hne]
      change e (e.symm (Pi.single p 1)) p = e (e.symm (Pi.single p 1)) q at h
      exact one_ne_zero (hp.symm.trans (h.trans hq))
    · intro f
      exact ⟨(⟨⊥, inferInstance⟩ : PrimeSpectrum K).comap f,
        splitAlgebraCoordinate_comap f⟩)

@[simp]
theorem splitAlgebraPointEquiv_apply (p : PrimeSpectrum B) :
    splitAlgebraPointEquiv (K := K) p = splitAlgebraCoordinate (K := K) p := rfl

end SplitAlgebra

section SeparableField

variable (k : Type u) (K : Type w) (L : Type v)
  [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L] [IsSepClosed K]

/-- A finite separable field extension is an étale algebra. -/
theorem finiteSeparable_etale : Algebra.Etale k L := by
  let := Algebra.FormallyEtale.of_isSeparable k L
  exact ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

/-- The spectrum of the separable tensor algebra is indexed by k-embeddings. -/
def separableTensorEmbeddingEquiv :
    PrimeSpectrum (K ⊗[k] L) ≃ (L →ₐ[k] K) := by
  let := finiteSeparable_etale k L
  exact (splitAlgebraPointEquiv (K := K)).trans (AlgHom.liftEquiv k K L K).symm

/-- Manuscript `lem:separable-tensor`, with exactly its embedding index set.
An algebraic closure is more than sufficient; separable closedness suffices. -/
def separableTensorEquiv : (K ⊗[k] L) ≃ₐ[K] ((L →ₐ[k] K) → K) := by
  let := finiteSeparable_etale k L
  exact (Algebra.FormallyEtale.equivPiOfIsSepClosed K (K ⊗[k] L)).trans
    (AlgEquiv.piCongrLeft' K (fun _ : PrimeSpectrum (K ⊗[k] L) => K)
      (separableTensorEmbeddingEquiv k K L))

/-- On pure tensors the splitting is the displayed evaluation map. -/
theorem separableTensorEquiv_tmul (c : K) (b : L) (τ : L →ₐ[k] K) :
    separableTensorEquiv k K L (c ⊗ₜ[k] b) τ = c * τ b := by
  let := finiteSeparable_etale k L
  let p := (separableTensorEmbeddingEquiv k K L).symm τ
  have h : (AlgHom.liftEquiv k K L K)
      (separableTensorEmbeddingEquiv k K L p) =
        splitAlgebraCoordinate (K := K) p := by
    exact (AlgHom.liftEquiv k K L K).apply_symm_apply _
  have hτ : separableTensorEmbeddingEquiv k K L p = τ :=
    (separableTensorEmbeddingEquiv k K L).apply_symm_apply τ
  rw [hτ] at h
  simp only [separableTensorEquiv, AlgEquiv.trans_apply,
    AlgEquiv.piCongrLeft'_apply, Equiv.piCongrLeft'_apply]
  change Algebra.FormallyEtale.equivPiOfIsSepClosed K (K ⊗[k] L)
    (c ⊗ₜ[k] b) p = c * τ b
  rw [← splitAlgebraCoordinate_apply, ← h, AlgHom.liftEquiv_tmul]
  rfl

/-- The coordinate formula holds for arbitrary tensors, using the canonical lift. -/
theorem separableTensorEquiv_apply (x : K ⊗[k] L) (τ : L →ₐ[k] K) :
    separableTensorEquiv k K L x τ = AlgHom.liftEquiv k K L K τ x := by
  induction x using TensorProduct.inductionOn with
  | tmul c b =>
    rw [separableTensorEquiv_tmul, AlgHom.liftEquiv_tmul]
    rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- The right L-action on each coordinate is multiplication by τ(b). -/
theorem separableTensorEquiv_mul_right (x : K ⊗[k] L) (b : L)
    (τ : L →ₐ[k] K) :
    separableTensorEquiv k K L (x * (1 ⊗ₜ[k] b)) τ =
      separableTensorEquiv k K L x τ * τ b := by
  rw [map_mul]
  simp only [Pi.mul_apply, separableTensorEquiv_tmul, one_mul]

/-- The primitive idempotent that selects the τ-factor. -/
def separableTensorIdempotent (τ : L →ₐ[k] K) : K ⊗[k] L := by
  classical
  exact (separableTensorEquiv k K L).symm (Pi.single τ 1)

@[simp]
theorem separableTensorEquiv_idempotent (τ : L →ₐ[k] K) :
    separableTensorEquiv k K L (separableTensorIdempotent k K L τ) =
      Pi.single τ 1 := by
  classical
  exact (separableTensorEquiv k K L).apply_symm_apply _

/-- Evaluation of the selected idempotent at its own embedding is one. -/
@[simp]
theorem separableTensorIdempotent_evaluation (τ : L →ₐ[k] K) :
    AlgHom.liftEquiv k K L K τ (separableTensorIdempotent k K L τ) = 1 := by
  classical
  rw [← separableTensorEquiv_apply, separableTensorEquiv_idempotent]
  simp

/-- Multiplication on the selected factor is scalar multiplication by evaluation. -/
theorem mul_separableTensorIdempotent (x : K ⊗[k] L) (τ : L →ₐ[k] K) :
    x * separableTensorIdempotent k K L τ =
      (AlgHom.liftEquiv k K L K τ x) • separableTensorIdempotent k K L τ := by
  classical
  apply (separableTensorEquiv k K L).injective
  ext ν
  simp only [map_mul, map_smul, separableTensorEquiv_idempotent,
    Pi.mul_apply, Pi.smul_apply]
  by_cases h : ν = τ
  · subst ν
    simp only [Pi.single_eq_same, mul_one, smul_eq_mul]
    exact separableTensorEquiv_apply k K L x τ
  · simp [h]

/-- The selected element is idempotent in the actual tensor algebra. -/
theorem separableTensorIdempotent_mul_self (τ : L →ₐ[k] K) :
    separableTensorIdempotent k K L τ * separableTensorIdempotent k K L τ =
      separableTensorIdempotent k K L τ := by
  rw [mul_separableTensorIdempotent, separableTensorIdempotent_evaluation, one_smul]

/-- Balancing relation needed to construct the separable summand inclusion. -/
theorem separableTensorIdempotent_mul_right (b : L) (τ : L →ₐ[k] K) :
    separableTensorIdempotent k K L τ * (1 ⊗ₜ[k] b) =
      τ b • separableTensorIdempotent k K L τ := by
  rw [mul_comm, mul_separableTensorIdempotent, AlgHom.liftEquiv_tmul, one_smul]

end SeparableField

end

end C3PerfectField
