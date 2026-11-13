module

public import C3PerfectField.GaloisBaseChange
public import C3PerfectField.FinitePrimeFields
public import C3PerfectField.CyclotomicPrimeFields
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.FieldTheory.PrimeField
public import Mathlib.Algebra.Algebra.ZMod

/-!
Manuscript Lemma `lem:cyclic-fg` and Proposition `prop:prime-orbits`.
The prime degree survives base change to the actual coefficient field.
The degree-one alternative is excluded by counting embeddings over its
finite transcendence basis.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

universe u v

variable {P : Type u} {F k : Type v} [Field P] [Field F] [Field k]
  [Algebra P F] [Algebra P k] [Algebra F k] [IsScalarTower P F k] [IsAlgClosed k]

/-- A Galois subfield contained in the coefficient field has degree bounded
by the coefficient field's degree over its rational parameters. -/
theorem galois_degree_le_of_contained (L : IntermediateField P k)
    [FiniteDimensional P L] [IsGalois P L] {t : Set F}
    (ht : AlgebraicIndepOn P id t)
    [FiniteDimensional (IntermediateField.adjoin P t) F]
    (hL : (L : Set k) ⊆ Set.range (algebraMap F k)) :
    Module.finrank P L ≤ Module.finrank (IntermediateField.adjoin P t) F := by
  classical
  let R := IntermediateField.adjoin P t
  let y : t → k := fun a => algebraMap F k a
  have hyP : AlgebraicIndependent P y :=
    ht.map' (f := IsScalarTower.toAlgHom P F k) (algebraMap F k).injective
  have hyL : AlgebraicIndependent L y := hyP.extendScalars L
  have hext (ρ : L ≃ₐ[P] L) :
      ∃ σ : k ≃+* k,
        (∀ a : L, σ (a : k) = (ρ a : k)) ∧ ∀ a ∈ Set.range y, σ a = a :=
    exists_ringEquiv_extension_fixing_independent hyL.coe_range ρ.toRingEquiv
  let σ (ρ : L ≃ₐ[P] L) := (hext ρ).choose
  have hσ (ρ : L ≃ₐ[P] L) :
      (∀ a : L, σ ρ (a : k) = (ρ a : k)) ∧
        ∀ a ∈ Set.range y, σ ρ a = a := (hext ρ).choose_spec
  have hfix (ρ : L ≃ₐ[P] L) :
      ∀ a ∈ R, σ ρ (algebraMap F k a) = algebraMap F k a := by
    apply IntermediateField.adjoin_le_subfield P t
      (K := RingHom.eqLocusField
        ((σ ρ).toRingHom.comp (algebraMap F k)) (algebraMap F k))
    · rintro _ ⟨a, rfl⟩
      change σ ρ (algebraMap F k (algebraMap P F a)) =
        algebraMap F k (algebraMap P F a)
      rw [← IsScalarTower.algebraMap_apply]
      have h := (hσ ρ).1 (algebraMap P L a)
      simpa only [ρ.commutes, IntermediateField.coe_algebraMap_apply] using h
    · intro a ha
      exact (hσ ρ).2 _ ⟨⟨a, ha⟩, rfl⟩
  let f (ρ : L ≃ₐ[P] L) : F →ₐ[R] k := {
    toRingHom := (σ ρ).toRingHom.comp (algebraMap F k)
    commutes' := fun a => by
      change σ ρ (algebraMap F k (algebraMap R F a)) = algebraMap R k a
      rw [← IsScalarTower.algebraMap_apply]
      exact hfix ρ a a.2
  }
  have hf : Function.Injective f := by
    intro ρ τ h
    apply AlgEquiv.ext
    intro a
    apply Subtype.ext
    obtain ⟨b, hb⟩ := hL a.2
    have hval := DFunLike.congr_fun h b
    change σ ρ (algebraMap F k b) = σ τ (algebraMap F k b) at hval
    rw [hb, (hσ ρ).1, (hσ τ).1] at hval
    exact hval
  calc
    Module.finrank P L = Nat.card (L ≃ₐ[P] L) :=
      (IsGalois.card_aut_eq_finrank P L).symm
    _ ≤ Nat.card (F →ₐ[R] k) := Nat.card_le_card_of_injective f hf
    _ ≤ Module.finrank R F := card_algHom_le_finrank R F k

/-- Every prime extension of the smaller base whose degree exceeds the
finite rational degree remains of that degree over the coefficient field. -/
theorem prime_degree_adjoin_coefficientField (L : IntermediateField P k)
    [FiniteDimensional P L] [IsGalois P L] {t : Set F}
    (ht : AlgebraicIndepOn P id t)
    [FiniteDimensional (IntermediateField.adjoin P t) F]
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hd : Module.finrank P L = ℓ)
    (hn : Module.finrank (IntermediateField.adjoin P t) F < ℓ) :
    Module.finrank F (IntermediateField.adjoin F (L : Set k)) = ℓ := by
  have hdiv := finrank_adjoin_dvd_of_isGalois L F
  rw [hd] at hdiv
  apply (hℓ.eq_one_or_self_of_dvd _ hdiv).resolve_left
  intro h1
  have hL := IntermediateField.finrank_adjoin_eq_one_iff.mp h1
  have hcontained : (L : Set k) ⊆ Set.range (algebraMap F k) :=
    fun a ha => IntermediateField.mem_bot.mp (hL ha)
  have hle := galois_degree_le_of_contained L ht hcontained
  rw [hd] at hle
  exact (not_le_of_gt hn) hle

variable [Field.FG F]

/-- A uniform rational-degree bound works for every sufficiently large
prime, once the smaller base supplies its prime Galois extensions. -/
theorem exists_prime_extension_bound
    (hprime : ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ 2 →
      ∃ L : IntermediateField P k,
        FiniteDimensional P L ∧ IsGalois P L ∧ Module.finrank P L = ℓ) :
    ∃ n : ℕ, ∀ (ℓ : ℕ), ℓ.Prime → max 2 n < ℓ →
      ∃ E : IntermediateField F k,
        FiniteDimensional F E ∧ IsGalois F E ∧ Module.finrank F E = ℓ ∧
          IsCyclic (E ≃ₐ[F] E) := by
  let : Algebra.EssFiniteType P F := essFiniteType_of_field_fg
  obtain ⟨t, _, ht, hfin⟩ := exists_finite_transcendenceBasis (P := P) (k := F)
  let := hfin
  refine ⟨Module.finrank (IntermediateField.adjoin P t) F, ?_⟩
  intro ℓ hℓ hbound
  have h2 : 2 < ℓ := lt_of_le_of_lt (le_max_left _ _) hbound
  have hn : Module.finrank (IntermediateField.adjoin P t) F < ℓ :=
    lt_of_le_of_lt (le_max_right _ _) hbound
  obtain ⟨L, hLfin, hLg, hLd⟩ := hprime ℓ hℓ (ne_of_gt h2)
  let := hLfin
  let := hLg
  let E := IntermediateField.adjoin F (L : Set k)
  have hEfin : FiniteDimensional F E := finiteDimensional_adjoin_of_finiteDimensional L F
  let := hEfin
  have hEg : IsGalois F E := isGalois_adjoin_of_isGalois L F
  let := hEg
  have hEd : Module.finrank F E = ℓ :=
    prime_degree_adjoin_coefficientField L ht.1 hℓ hLd hn
  have hcard : Nat.card (E ≃ₐ[F] E) = ℓ :=
    (IsGalois.card_aut_eq_finrank F E).trans hEd
  let : Fact ℓ.Prime := ⟨hℓ⟩
  exact ⟨E, hEfin, hEg, hEd, isCyclic_of_prime_card hcard⟩

/-- Characteristic zero: all sufficiently large primes occur as exact
ambient periods under automorphisms fixing the full coefficient field. -/
theorem exists_large_prime_period_characteristic_zero [CharZero k]
    [CharZero F] (B : ℕ) :
    ∃ (ℓ : ℕ) (σ : k ≃ₐ[F] k) (lambda : k),
      ℓ.Prime ∧ B < ℓ ∧ Function.minimalPeriod σ lambda = ℓ := by
  let : Algebra.EssFiniteType ℚ F := essFiniteType_of_field_fg
  obtain ⟨t, _, ht, hfin⟩ := exists_finite_transcendenceBasis (P := ℚ) (k := F)
  let := hfin
  obtain ⟨ℓ, hbound, hℓ⟩ :=
    Nat.exists_infinite_primes (max B (max 2 (Module.finrank (IntermediateField.adjoin ℚ t) F)) + 1)
  have hB : B < ℓ := lt_of_lt_of_le (Nat.lt_succ_of_le (le_max_left _ _)) hbound
  have h2 : 2 < ℓ := lt_of_lt_of_le
    (Nat.lt_succ_of_le ((le_max_left _ _).trans (le_max_right _ _))) hbound
  have hn : Module.finrank (IntermediateField.adjoin ℚ t) F < ℓ :=
    lt_of_lt_of_le (Nat.lt_succ_of_le ((le_max_right _ _).trans (le_max_right _ _))) hbound
  obtain ⟨L, hLfin, hLg, hLd⟩ :=
    exists_prime_galois_subfield_characteristic_zero (k := k) hℓ (ne_of_gt h2)
  let := hLfin
  let := hLg
  let M := IntermediateField.adjoin F (L : Set k)
  let := finiteDimensional_adjoin_of_finiteDimensional L F
  let := isGalois_adjoin_of_isGalois L F
  have hd : Module.finrank F M = ℓ :=
    prime_degree_adjoin_coefficientField L ht.1 hℓ hLd hn
  obtain ⟨σ, lambda, hper⟩ := exists_ambient_prime_period_of_prime_degree (k := k) hℓ hd
  exact ⟨ℓ, σ, lambda, hℓ, hB, hper⟩

/-- Positive characteristic: the finite-field prime extensions yield
arbitrarily large exact periods fixing the full coefficient field. -/
theorem exists_large_prime_period_positive_characteristic
    (p : ℕ) [Fact p.Prime] [Algebra (ZMod p) F] [Algebra (ZMod p) k]
    [IsScalarTower (ZMod p) F k] (B : ℕ) :
    ∃ (ℓ : ℕ) (σ : k ≃ₐ[F] k) (lambda : k),
      ℓ.Prime ∧ B < ℓ ∧ Function.minimalPeriod σ lambda = ℓ := by
  let : Algebra.EssFiniteType (ZMod p) F := essFiniteType_of_field_fg
  obtain ⟨t, _, ht, hfin⟩ := exists_finite_transcendenceBasis (P := ZMod p) (k := F)
  let := hfin
  obtain ⟨ℓ, hbound, hℓ⟩ :=
    Nat.exists_infinite_primes
      (max B (Module.finrank (IntermediateField.adjoin (ZMod p) t) F) + 1)
  have hB : B < ℓ := lt_of_lt_of_le (Nat.lt_succ_of_le (le_max_left _ _)) hbound
  have hn : Module.finrank (IntermediateField.adjoin (ZMod p) t) F < ℓ :=
    lt_of_lt_of_le (Nat.lt_succ_of_le (le_max_right _ _)) hbound
  obtain ⟨L, hLfin, hLg, hLd⟩ :=
    exists_finite_galois_subfield (k := k) p ℓ hℓ.ne_zero
  let := hLfin
  let := hLg
  let M := IntermediateField.adjoin F (L : Set k)
  let := finiteDimensional_adjoin_of_finiteDimensional L F
  let := isGalois_adjoin_of_isGalois L F
  have hd : Module.finrank F M = ℓ :=
    prime_degree_adjoin_coefficientField L ht.1 hℓ hLd hn
  obtain ⟨σ, lambda, hper⟩ := exists_ambient_prime_period_of_prime_degree (k := k) hℓ hd
  exact ⟨ℓ, σ, lambda, hℓ, hB, hper⟩

/-- Manuscript Proposition `prop:prime-orbits`, for an actual finitely
generated subfield of the algebraically closed ambient field. -/
theorem exists_large_prime_period (F₀ : Subfield k) [Field.FG F₀] (B : ℕ) :
    ∃ (ℓ : ℕ) (σ : k ≃ₐ[F₀] k) (lambda : k),
      ℓ.Prime ∧ B < ℓ ∧ Function.minimalPeriod σ lambda = ℓ := by
  obtain ⟨p, hp⟩ := CharP.exists k
  let := hp
  rcases CharP.char_is_prime_or_zero k p with hprime | rfl
  · let : Fact p.Prime := ⟨hprime⟩
    let aK : Algebra (ZMod p) k := ZMod.algebra k p
    let aF : Algebra (ZMod p) F₀ := ZMod.algebra F₀ p
    let aFK : Algebra F₀ k := inferInstance
    let hT : @IsScalarTower (ZMod p) F₀ k aF.toSMul aFK.toSMul aK.toSMul :=
      @ZMod.instIsScalarTower p F₀ k _ _ aF.toModule aK.toModule aFK.toModule
    exact @exists_large_prime_period_positive_characteristic
      F₀ k _ _ aFK _ _ p _ aF aK hT B
  · let : CharZero k := CharP.charP_to_charZero k
    exact exists_large_prime_period_characteristic_zero (F := F₀) B

/-- Manuscript Lemma `lem:cyclic-fg`: every sufficiently large prime is
the degree of a cyclic Galois extension inside the given ambient field. -/
theorem exists_cyclic_prime_extension (F₀ : Subfield k) [Field.FG F₀] :
    ∃ n : ℕ, ∀ (ℓ : ℕ), ℓ.Prime → max 2 n < ℓ →
      ∃ E : IntermediateField F₀ k,
        FiniteDimensional F₀ E ∧ IsGalois F₀ E ∧ Module.finrank F₀ E = ℓ ∧
          IsCyclic (E ≃ₐ[F₀] E) := by
  obtain ⟨p, hp⟩ := CharP.exists k
  let := hp
  rcases CharP.char_is_prime_or_zero k p with hprime | rfl
  · let : Fact p.Prime := ⟨hprime⟩
    let aK : Algebra (ZMod p) k := ZMod.algebra k p
    let aF : Algebra (ZMod p) F₀ := ZMod.algebra F₀ p
    let aFK : Algebra F₀ k := inferInstance
    -- Subtypes also carry scalar actions from additive subgroup classes;
    -- specify the algebra actions used by the field-extension theorem.
    let hT : @IsScalarTower (ZMod p) F₀ k aF.toSMul aFK.toSMul aK.toSMul :=
      @ZMod.instIsScalarTower p F₀ k _ _ aF.toModule aK.toModule aFK.toModule
    exact @exists_prime_extension_bound (ZMod p) F₀ k _ _ _ aF aK aFK hT _ _
      (fun ℓ hℓ _ => exists_finite_galois_subfield (k := k) p ℓ hℓ.ne_zero)
  · let : CharZero k := CharP.charP_to_charZero k
    exact exists_prime_extension_bound (P := ℚ) (F := F₀)
      (fun _ hℓ hodd => exists_prime_galois_subfield_characteristic_zero hℓ hodd)

/-- In particular a finite coefficient list admits arbitrarily large
prime orbits while every listed coefficient is fixed. -/
theorem exists_large_prime_period_fixing_coefficients (S : Finset k) (B : ℕ) :
    ∃ (ℓ : ℕ) (σ : k ≃+* k) (lambda : k),
      ℓ.Prime ∧ B < ℓ ∧ Function.minimalPeriod σ lambda = ℓ ∧
        ∀ a ∈ S, σ a = a := by
  let := coefficientField_fg S
  obtain ⟨ℓ, σ, lambda, hℓ, hB, hper⟩ :=
    exists_large_prime_period (coefficientField S) B
  refine ⟨ℓ, σ.toRingEquiv, lambda, hℓ, hB, hper, ?_⟩
  intro a ha
  exact σ.commutes (⟨a, mem_coefficientField ha⟩ : coefficientField S)

end C3PerfectField
