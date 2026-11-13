module

public import C3PerfectField.FieldAutomorphismExtension
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.OrderOfElement

/-!
The last Galois-theoretic step of manuscript Proposition `prop:prime-orbits`:
a prime-degree Galois extension yields an exact prime period, and that period
survives extension to an arbitrary algebraically closed ambient field.
`PrimeCoefficientOrbits` constructs the required extensions over every
finitely generated coefficient subfield. No such extension is a hypothesis
of the target AR theorem.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

universe u v w

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

/-- A nonidentity automorphism whose prime power is the identity has a
point with exact period that prime. -/
theorem exists_prime_period_of_prime_order (ρ : E ≃ₐ[F] E) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hpow : ρ ^ ℓ = 1) (hρ : ρ ≠ 1) :
    ∃ a : E, Function.minimalPeriod ρ a = ℓ := by
  have hmoved : ∃ a : E, ρ a ≠ a := by
    by_contra h
    apply hρ
    apply AlgEquiv.ext
    intro a
    exact not_exists_not.mp h a
  obtain ⟨a, ha⟩ := hmoved
  refine ⟨a, ?_⟩
  have hdvd : Function.minimalPeriod ρ a ∣ ℓ := by
    apply (iterate_eq_iff_period_dvd ρ a ℓ).mp
    rw [← AlgEquiv.coe_pow, hpow, AlgEquiv.one_apply]
  apply (hℓ.eq_one_or_self_of_dvd _ hdvd).resolve_left
  intro hper
  exact ha ((Function.minimalPeriod_eq_one_iff_isFixedPt.mp hper) : ρ a = a)

/-- Galois theory supplies a nonidentity automorphism and its prime power
relation from the actual degree, rather than assuming orbit witnesses. -/
theorem exists_prime_period_of_prime_degree [FiniteDimensional F E] [IsGalois F E]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hdegree : Module.finrank F E = ℓ) :
    ∃ (ρ : E ≃ₐ[F] E) (a : E), Function.minimalPeriod ρ a = ℓ := by
  classical
  have hcard : Nat.card (E ≃ₐ[F] E) = ℓ :=
    (IsGalois.card_aut_eq_finrank F E).trans hdegree
  have hn : ¬Subsingleton (E ≃ₐ[F] E) := by
    intro hs
    let := hs
    have h1 := Nat.card_of_subsingleton (1 : E ≃ₐ[F] E)
    exact hℓ.ne_one (hcard.symm.trans h1)
  let : Nontrivial (E ≃ₐ[F] E) := not_subsingleton_iff_nontrivial.mp hn
  obtain ⟨ρ, hρ⟩ := exists_ne (1 : E ≃ₐ[F] E)
  have hpow : ρ ^ ℓ = 1 := hcard ▸ (pow_card_eq_one' (x := ρ))
  obtain ⟨a, ha⟩ := exists_prime_period_of_prime_order ρ hℓ hpow hρ
  exact ⟨ρ, a, ha⟩

variable {k : Type w} [Field k] [IsAlgClosed k] [Algebra F k] [Algebra E k]
  [IsScalarTower F E k]

/-- The witness in a prime-degree Galois subextension produces an ambient
`F`-automorphism and an ambient point with exactly the same prime period. -/
theorem exists_ambient_prime_period_of_prime_degree [FiniteDimensional F E] [IsGalois F E]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hdegree : Module.finrank F E = ℓ) :
    ∃ (σ : k ≃ₐ[F] k) (lambda : k), Function.minimalPeriod σ lambda = ℓ := by
  obtain ⟨ρ, a, ha⟩ := exists_prime_period_of_prime_degree hℓ hdegree
  obtain ⟨σ, hσ⟩ := exists_algEquiv_extension (k := k) ρ
  refine ⟨σ, algebraMap E k a, ?_⟩
  exact (minimalPeriod_extension ρ.toRingEquiv σ.toRingEquiv hσ a).trans ha

end C3PerfectField
