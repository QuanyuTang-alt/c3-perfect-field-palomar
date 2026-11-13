module

public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic

/-!
Elementary period arithmetic used in the manuscript's weighted graph argument.
This module does not assert the algebra or Auslander–Reiten theorem.
-/

@[expose] public section

namespace C3PerfectField

open Function

universe u
variable {V : Type u}

/-- Manuscript Lemma `lem:power-period`, divisibility part. -/
theorem iterate_eq_iff_period_dvd (f : V → V) (v : V) (q : ℕ) :
    f^[q] v = v ↔ minimalPeriod f v ∣ q := by
  exact isPeriodicPt_iff_minimalPeriod_dvd

/-- Manuscript Lemma `lem:power-period`, period of a power. -/
theorem period_of_power (f : V → V) (v : V) (a : ℕ) (ha : 0 < a) :
    minimalPeriod f^[a] v = minimalPeriod f v / Nat.gcd a (minimalPeriod f v) := by
  simpa only [Nat.gcd_comm] using
    (minimalPeriod_iterate_eq_div_gcd (f := f) (x := v) (Nat.ne_of_gt ha))

/-- Arithmetic step of `prop:prime-invariant`: a large prime cannot divide
exactly one of two positive periods satisfying the adjacent-period bound.
The bound is an explicit premise of this arithmetic lemma, not a premise
added to the main theorem. -/
theorem prime_dvd_iff_of_adjacent_bound
    (m n C p : ℕ) (hm : 0 < m) (hn : 0 < n) (hp : Nat.Prime p)
    (hlarge : C ^ 2 < p)
    (hbound : (m / Nat.gcd m n) * (n / Nat.gcd m n) ≤ C ^ 2) :
    (p ∣ m ↔ p ∣ n) := by
  have one_way : ∀ (a b : ℕ), 0 < a → 0 < b →
      (a / Nat.gcd a b) * (b / Nat.gcd a b) ≤ C ^ 2 →
      p ∣ a → p ∣ b := by
    intro a b ha hb hab hpa
    by_contra hpb
    have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b ha
    have hpg : ¬ p ∣ Nat.gcd a b :=
      fun h => hpb (dvd_trans h (Nat.gcd_dvd_right a b))
    have hfactor : p ∣ a / Nat.gcd a b := by
      have : p ∣ (a / Nat.gcd a b) * Nat.gcd a b := by
        simpa only [Nat.div_mul_cancel (Nat.gcd_dvd_left a b)] using hpa
      exact (hp.dvd_mul.mp this).resolve_right hpg
    have hapos : 0 < a / Nat.gcd a b := by
      exact Nat.div_pos (Nat.gcd_le_left b ha) hg
    have hbpos : 0 < b / Nat.gcd a b := by
      exact Nat.div_pos (Nat.gcd_le_right a hb) hg
    have hple : p ≤ a / Nat.gcd a b := Nat.le_of_dvd hapos hfactor
    have hprod : p ≤ (a / Nat.gcd a b) * (b / Nat.gcd a b) := by
      nlinarith
    omega
  constructor
  · exact one_way m n hm hn hbound
  · apply one_way n m hn hm
    simpa only [Nat.gcd_comm, Nat.mul_comm] using hbound

end C3PerfectField
