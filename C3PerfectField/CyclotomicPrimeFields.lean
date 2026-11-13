module

public import C3PerfectField.PrimeGaloisOrbits
public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
The characteristic-zero case of manuscript Lemma `lem:prime-field`.
In the cyclotomic field of order `ℓ²`, the subgroup of `ℓ`th powers
has index `ℓ`. Its fixed field is Galois of degree `ℓ`, and embeds
as an actual subfield in every algebraically closed field of characteristic zero.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

universe u

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]

/-- The fixed field of the power subgroup in the `ℓ²` cyclotomic field
realizes a Galois extension of the rational prime field of degree `ℓ`. -/
theorem exists_prime_galois_subfield_characteristic_zero {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) :
    ∃ L : IntermediateField ℚ k,
      FiniteDimensional ℚ L ∧ IsGalois ℚ L ∧ Module.finrank ℚ L = ℓ := by
  classical
  let : NeZero (ℓ ^ 2) := ⟨pow_ne_zero 2 hℓ.ne_zero⟩
  let C := CyclotomicField (ℓ ^ 2) ℚ
  let : FiniteDimensional ℚ C :=
    IsCyclotomicExtension.finiteDimensional {(ℓ ^ 2)} ℚ C
  let : IsGalois ℚ C := IsCyclotomicExtension.isGalois {(ℓ ^ 2)} ℚ C
  let e : (C ≃ₐ[ℚ] C) ≃* (ZMod (ℓ ^ 2))ˣ :=
    IsCyclotomicExtension.autEquivPow C
      (Polynomial.cyclotomic.irreducible_rat (pow_pos hℓ.pos 2))
  let : IsCyclic (ZMod (ℓ ^ 2))ˣ :=
    ZMod.isCyclic_units_of_prime_pow ℓ hℓ hodd 2
  let H₀ := (powMonoidHom ℓ : (ZMod (ℓ ^ 2))ˣ →* (ZMod (ℓ ^ 2))ˣ).range
  let H := H₀.comap e.toMonoidHom
  have hcard : Nat.card (ZMod (ℓ ^ 2))ˣ = ℓ * (ℓ - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      show ℓ ^ 2 = ℓ ^ (1 + 1) from rfl, Nat.totient_prime_pow_succ hℓ]
    simp only [pow_one]
  have hi : H.index = ℓ := by
    calc
      H.index = H₀.index := H₀.index_comap_of_surjective e.surjective
      _ = ℓ := by
        change (powMonoidHom ℓ : (ZMod (ℓ ^ 2))ˣ →* (ZMod (ℓ ^ 2))ˣ).range.index = ℓ
        rw [IsCyclic.index_powMonoidHom_range, hcard, Nat.gcd_eq_right]
        exact dvd_mul_right ℓ (ℓ - 1)
  let L₀ := IntermediateField.fixedField H
  have hd : Module.finrank ℚ L₀ = ℓ := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,
      IntermediateField.fixingSubgroup_fixedField]
    exact hi
  let f : L₀ →ₐ[ℚ] k := IsAlgClosed.lift
  let L := f.fieldRange
  let i : L₀ ≃ₐ[ℚ] L := AlgEquiv.ofInjectiveField f
  have hfin : FiniteDimensional ℚ L := i.toLinearEquiv.finiteDimensional
  let := hfin
  have hg : IsGalois ℚ L := IsGalois.of_algEquiv i
  refine ⟨L, hfin, hg, ?_⟩
  exact i.toLinearEquiv.finrank_eq.symm.trans hd

/-- The characteristic-zero prime-field construction supplies a point
of exact period `ℓ` under an automorphism of the actual ambient field. -/
theorem exists_prime_period_characteristic_zero {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hodd : ℓ ≠ 2) :
    ∃ (σ : k ≃ₐ[ℚ] k) (lambda : k), Function.minimalPeriod σ lambda = ℓ := by
  obtain ⟨L, hfin, hg, hd⟩ :=
    exists_prime_galois_subfield_characteristic_zero (k := k) hℓ hodd
  let := hfin
  let := hg
  exact exists_ambient_prime_period_of_prime_degree (k := k) hℓ hd

end C3PerfectField
