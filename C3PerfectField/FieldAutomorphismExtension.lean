module

public import C3PerfectField.CoefficientFields
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.MvPolynomial.Equiv
public import C3PerfectField.PeriodArithmetic

/-!
Manuscript Lemma `lem:extend-overfield`.
The extension works for any subfield automorphism: choose a transcendence
basis, act on the polynomial coefficients, then extend to the algebraic
closure. No algebraicity hypothesis is imposed on the ambient field.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

universe u v w

variable {E : Type u} {k : Type v} [Field E] [Field k] [Algebra E k]
  {ι : Type w} {x : ι → k}

/-- Acting on coefficients and fixing an algebraically independent family. -/
noncomputable def adjoinCoefficientsAut (hx : AlgebraicIndependent E x) (ρ : E ≃+* E) :
    Algebra.adjoin E (Set.range x) ≃+* Algebra.adjoin E (Set.range x) :=
  hx.aevalEquiv.toRingEquiv.symm.trans
    ((MvPolynomial.mapEquiv ι ρ).trans hx.aevalEquiv.toRingEquiv)

theorem adjoinCoefficientsAut_algebraMap (hx : AlgebraicIndependent E x)
    (ρ : E ≃+* E) (a : E) :
    adjoinCoefficientsAut hx ρ (algebraMap E (Algebra.adjoin E (Set.range x)) a) =
      algebraMap E (Algebra.adjoin E (Set.range x)) (ρ a) := by
  change hx.aevalEquiv (MvPolynomial.map ρ
    (hx.aevalEquiv.symm (algebraMap E (Algebra.adjoin E (Set.range x)) a))) = _
  rw [← hx.aevalEquiv.commutes a, AlgEquiv.symm_apply_apply]
  simp only [MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
  exact hx.aevalEquiv.commutes (ρ a)

/-- Coefficient automorphisms fix all of the polynomial variables. -/
theorem adjoinCoefficientsAut_variable (hx : AlgebraicIndependent E x)
    (ρ : E ≃+* E) (i : ι) :
    adjoinCoefficientsAut hx ρ (hx.aevalEquiv (MvPolynomial.X i)) =
      hx.aevalEquiv (MvPolynomial.X i) := by
  change hx.aevalEquiv (MvPolynomial.map ρ
    (hx.aevalEquiv.symm (hx.aevalEquiv (MvPolynomial.X i)))) = _
  rw [AlgEquiv.symm_apply_apply, MvPolynomial.map_X]

/-- An extension can be chosen to fix a prescribed transcendence basis. -/
theorem exists_ringEquiv_extension_of_basis [IsAlgClosed k]
    (hx : IsTranscendenceBasis E x) (ρ : E ≃+* E) :
    ∃ σ : k ≃+* k,
      (∀ a : E, σ (algebraMap E k a) = algebraMap E k (ρ a)) ∧
        ∀ i, σ (x i) = x i := by
  let D := Algebra.adjoin E (Set.range x)
  let : IsAlgClosure D k := {
    isAlgClosed := inferInstance
    isAlgebraic := hx.isAlgebraic
  }
  let e : D ≃+* D := adjoinCoefficientsAut hx.1 ρ
  let σ : k ≃+* k := IsAlgClosure.equivOfEquiv k k e
  refine ⟨σ, ?_, ?_⟩
  · intro a
    have h := IsAlgClosure.equivOfEquiv_algebraMap k k e (algebraMap E D a)
    rw [show e (algebraMap E D a) = algebraMap E D (ρ a) from
      adjoinCoefficientsAut_algebraMap hx.1 ρ a] at h
    simpa only [← IsScalarTower.algebraMap_apply E D k] using h
  · intro i
    have h := IsAlgClosure.equivOfEquiv_algebraMap k k e
      (hx.1.aevalEquiv (MvPolynomial.X i))
    rw [show e (hx.1.aevalEquiv (MvPolynomial.X i)) =
      hx.1.aevalEquiv (MvPolynomial.X i) from
      adjoinCoefficientsAut_variable hx.1 ρ i] at h
    have hv : algebraMap D k (hx.1.aevalEquiv (MvPolynomial.X i)) = x i := by
      change MvPolynomial.aeval x (MvPolynomial.X i) = x i
      exact MvPolynomial.aeval_X x i
    change σ (algebraMap D k (hx.1.aevalEquiv (MvPolynomial.X i))) =
      algebraMap D k (hx.1.aevalEquiv (MvPolynomial.X i)) at h
    rw [hv] at h
    exact h

/-- One may also fix any algebraically independent set: extend it to a
transcendence basis before applying the coefficient action. -/
theorem exists_ringEquiv_extension_fixing_independent [IsAlgClosed k]
    {s : Set k} (hs : AlgebraicIndepOn E id s) (ρ : E ≃+* E) :
    ∃ σ : k ≃+* k,
      (∀ a : E, σ (algebraMap E k a) = algebraMap E k (ρ a)) ∧
        ∀ a ∈ s, σ a = a := by
  obtain ⟨t, hst, ht⟩ := exists_isTranscendenceBasis_superset hs
  obtain ⟨σ, hσ, hfix⟩ := exists_ringEquiv_extension_of_basis ht ρ
  exact ⟨σ, hσ, fun a ha => hfix ⟨a, hst ha⟩⟩

/-- Every automorphism of a subfield extends to an automorphism of the
entire algebraically closed ambient field, even if it is transcendental. -/
theorem exists_ringEquiv_extension [IsAlgClosed k] (ρ : E ≃+* E) :
    ∃ σ : k ≃+* k, ∀ a : E, σ (algebraMap E k a) = algebraMap E k (ρ a) := by
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis E k
  obtain ⟨σ, hσ, _⟩ := exists_ringEquiv_extension_of_basis ht ρ
  exact ⟨σ, hσ⟩

variable {F : Type w} [Field F] [Algebra F E] [Algebra F k] [IsScalarTower F E k]

/-- The extension preserves the field fixed by the original automorphism.
This supplies `lem:extend-overfield` for every finite Galois subextension
without requiring either finiteness or normality as extra premises. -/
theorem exists_algEquiv_extension [IsAlgClosed k] (ρ : E ≃ₐ[F] E) :
    ∃ σ : k ≃ₐ[F] k, ∀ a : E, σ (algebraMap E k a) = algebraMap E k (ρ a) := by
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_extension (k := k) ρ.toRingEquiv
  let τ : k ≃ₐ[F] k := {
    σ with
    commutes' := by
      intro a
      change σ (algebraMap F k a) = algebraMap F k a
      rw [IsScalarTower.algebraMap_apply F E k, hσ]
      exact congrArg (algebraMap E k) (ρ.commutes a)
  }
  exact ⟨τ, hσ⟩

/-- Restriction-compatible automorphisms have exactly the same point
period on the subfield and its image in the ambient field. -/
theorem minimalPeriod_extension (ρ : E ≃+* E) (σ : k ≃+* k)
    (hσ : ∀ a : E, σ (algebraMap E k a) = algebraMap E k (ρ a)) (a : E) :
    Function.minimalPeriod σ (algebraMap E k a) = Function.minimalPeriod ρ a := by
  have hiter (n : ℕ) :
      σ^[n] (algebraMap E k a) = algebraMap E k (ρ^[n] a) := by
    induction n with
    | zero => rfl
    | succ n hn =>
      rw [Function.iterate_succ_apply', hn, hσ, Function.iterate_succ_apply']
  apply Nat.dvd_antisymm
  · apply (iterate_eq_iff_period_dvd σ (algebraMap E k a) _).mp
    rw [hiter, Function.iterate_minimalPeriod]
  · apply (iterate_eq_iff_period_dvd ρ a _).mp
    apply (algebraMap E k).injective
    rw [← hiter, Function.iterate_minimalPeriod]

end C3PerfectField
