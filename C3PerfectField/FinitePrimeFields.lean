module

public import C3PerfectField.PrimeGaloisOrbits
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
The positive-characteristic case of manuscript Lemma `lem:prime-field`.
The splitting field of `X^(p^n) - X` is embedded in the actual ambient
algebraically closed field, and its degree and Galois property are transported
to that image. These are genuine subfields, not abstract orbit assumptions.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

universe u

variable (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [IsAlgClosed k]
  [Algebra (ZMod p) k]

/-- Every positive degree finite field extension of the prime field occurs
inside the given algebraically closed field of characteristic `p`. -/
theorem exists_finite_galois_subfield (n : ℕ) (hn : n ≠ 0) :
    ∃ L : IntermediateField (ZMod p) k,
      FiniteDimensional (ZMod p) L ∧ IsGalois (ZMod p) L ∧
        Module.finrank (ZMod p) L = n := by
  let f : GaloisField p n →ₐ[ZMod p] k := IsAlgClosed.lift
  let L := f.fieldRange
  let e : GaloisField p n ≃ₐ[ZMod p] L := AlgEquiv.ofInjectiveField f
  have hfin : FiniteDimensional (ZMod p) L := e.toLinearEquiv.finiteDimensional
  let := hfin
  have hg : IsGalois (ZMod p) L := IsGalois.of_algEquiv e
  refine ⟨L, hfin, hg, ?_⟩
  exact e.toLinearEquiv.finrank_eq.symm.trans (GaloisField.finrank p hn)

/-- The prime-degree subfield gives an exact prime orbit in the actual
ambient field, under an automorphism fixing its prime field. -/
theorem exists_prime_period_positive_characteristic {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ (σ : k ≃ₐ[ZMod p] k) (lambda : k), Function.minimalPeriod σ lambda = ℓ := by
  obtain ⟨L, hfin, hg, hd⟩ := exists_finite_galois_subfield (k := k) p ℓ hℓ.ne_zero
  let := hfin
  let := hg
  exact exists_ambient_prime_period_of_prime_degree (k := k) hℓ hd

end C3PerfectField
