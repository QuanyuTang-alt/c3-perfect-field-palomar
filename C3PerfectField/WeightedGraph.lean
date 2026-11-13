module

public import C3PerfectField.PeriodArithmetic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
The weighted graph section of the manuscript, independently of its representation
theory inputs. In particular, the bounds below are proved from the two weighted
neighbor sums, rather than postulated as adjacent-period bounds.
-/

@[expose] public section

namespace C3PerfectField

open Function
open scoped BigOperators

universe u

/-- Manuscript Definition `def:weighted`. Arrows may include loops. -/
structure WeightedDigraph (V : Type u) where
  arrow : V → V → Prop
  predecessors : V → Finset V
  successors : V → Finset V
  mem_predecessors : ∀ x y, x ∈ predecessors y ↔ arrow x y
  mem_successors : ∀ x y, y ∈ successors x ↔ arrow x y
  weight : V → ℕ
  weight_pos : ∀ x, 0 < weight x
  bound : ℕ
  bound_pos : 0 < bound
  predecessor_bound : ∀ y, ∑ x ∈ predecessors y, weight x ≤ bound * weight y
  successor_bound : ∀ x, ∑ y ∈ successors x, weight y ≤ bound * weight x

namespace WeightedDigraph

variable {V : Type u} (G : WeightedDigraph V)

/-- Removing loops does not change connected components. -/
def underlyingGraph : SimpleGraph V where
  Adj x y := x ≠ y ∧ (G.arrow x y ∨ G.arrow y x)
  symm := by
    constructor
    intro x y h
    exact ⟨Ne.symm h.1, h.2.symm⟩
  loopless := ⟨by simp⟩

/-- A bijection preserving arrows and weights, as in `def:weighted`. -/
structure Automorphism where
  perm : Equiv.Perm V
  arrow_iff : ∀ x y, G.arrow (perm x) (perm y) ↔ G.arrow x y
  weight_eq : ∀ x, G.weight (perm x) = G.weight x

variable (φ : G.Automorphism)

theorem arrow_iterate {x y : V} (h : G.arrow x y) (j : ℕ) :
    G.arrow (φ.perm^[j] x) (φ.perm^[j] y) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    simpa only [iterate_succ_apply'] using (φ.arrow_iff _ _).mpr ih

theorem weight_iterate (x : V) (j : ℕ) :
    G.weight (φ.perm^[j] x) = G.weight x := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simpa only [iterate_succ_apply', φ.weight_eq] using ih

/-- An injective map whose forward orbit lies in a finite set has a positive
return time. This is the pigeonhole step in `lem:period-propagation`. -/
theorem periodic_of_finite_iterates (f : V → V) (hf : Injective f) (x : V)
    (s : Finset V) (hs : ∀ j : ℕ, f^[j] x ∈ s) :
    x ∈ periodicPts f := by
  classical
  let orbit : ℕ → {y // y ∈ s} := fun j => ⟨f^[j] x, hs j⟩
  obtain ⟨a, b, hab, hne⟩ : ∃ a b, orbit a = orbit b ∧ a ≠ b := by
    simpa [Injective] using (not_injective_infinite_finite orbit)
  have heq : f^[a] x = f^[b] x := congrArg Subtype.val hab
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact mk_mem_periodicPts (Nat.sub_pos_of_lt hlt) (iterate_cancel hf heq.symm)
  · exact mk_mem_periodicPts (Nat.sub_pos_of_lt hlt) (iterate_cancel hf heq)

/-- Periodicity propagates across an undirected edge. -/
theorem periodic_of_adjacent {x y : V}
    (hxy : G.underlyingGraph.Adj x y) (hx : x ∈ periodicPts φ.perm) :
    y ∈ periodicPts φ.perm := by
  classical
  let m := minimalPeriod φ.perm x
  have hm : 0 < m := minimalPeriod_pos_of_mem_periodicPts hx
  have hfix : IsPeriodicPt φ.perm m x := isPeriodicPt_minimalPeriod _ _
  have hneighbor : ∀ j, φ.perm^[m]^[j] y ∈ G.predecessors x ∪ G.successors x := by
    intro j
    have hfixed : φ.perm^[m * j] x = x := hfix.mul_const j
    rcases hxy.2 with h | h
    · apply Finset.mem_union.mpr
      right
      apply (G.mem_successors _ _).mpr
      simpa only [← iterate_mul, hfixed] using G.arrow_iterate φ h (m * j)
    · apply Finset.mem_union.mpr
      left
      apply (G.mem_predecessors _ _).mpr
      simpa only [← iterate_mul, hfixed] using G.arrow_iterate φ h (m * j)
  have hy := periodic_of_finite_iterates φ.perm^[m] (φ.perm.injective.iterate m) y
    (G.predecessors x ∪ G.successors x) hneighbor
  obtain ⟨j, hj, hreturn⟩ := mem_periodicPts.mp hy
  apply mk_mem_periodicPts (Nat.mul_pos hm hj)
  simpa only [IsPeriodicPt, ← iterate_mul] using hreturn

/-- Manuscript Lemma `lem:period-propagation`, for connected vertices. -/
theorem periodic_of_reachable {x y : V} (hxy : G.underlyingGraph.Reachable x y)
    (hx : x ∈ periodicPts φ.perm) : y ∈ periodicPts φ.perm := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact hx
  | cons h p ih => exact ih (G.periodic_of_adjacent φ h hx)

/-- Count a power orbit using its minimal period and weight invariance. -/
theorem orbit_weight_le (a : ℕ) (x : V) (s : Finset V)
    (hs : ∀ j : ℕ, φ.perm^[a]^[j] x ∈ s) :
    minimalPeriod φ.perm^[a] x * G.weight x ≤ ∑ y ∈ s, G.weight y := by
  classical
  let n := minimalPeriod φ.perm^[a] x
  let f : ℕ → V := fun j => φ.perm^[a]^[j] x
  have hinj : Set.InjOn f (Finset.range n) := by
    intro i hi j hj hij
    exact iterate_injOn_Iio_minimalPeriod (by simpa using hi) (by simpa using hj) hij
  have hsub : (Finset.range n).image f ⊆ s := by
    intro y hy
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact hs j
  calc
    n * G.weight x = ∑ j ∈ Finset.range n, G.weight (f j) := by
      simp [f, ← iterate_mul, G.weight_iterate φ, Nat.mul_comm]
    _ = ∑ y ∈ (Finset.range n).image f, G.weight y :=
      (Finset.sum_image hinj).symm
    _ ≤ ∑ y ∈ s, G.weight y := Finset.sum_le_sum_of_subset hsub

/-- Manuscript Lemma `lem:adjacent-periods`, with a directed edge. -/
theorem adjacent_period_bound_of_arrow {x y : V} (hxy : G.arrow x y)
    (hx : x ∈ periodicPts φ.perm) (hy : y ∈ periodicPts φ.perm) :
    (minimalPeriod φ.perm x / Nat.gcd (minimalPeriod φ.perm x) (minimalPeriod φ.perm y)) *
      (minimalPeriod φ.perm y / Nat.gcd (minimalPeriod φ.perm x) (minimalPeriod φ.perm y)) ≤
      G.bound ^ 2 := by
  let m := minimalPeriod φ.perm x
  let n := minimalPeriod φ.perm y
  have hm : 0 < m := minimalPeriod_pos_of_mem_periodicPts hx
  have hn : 0 < n := minimalPeriod_pos_of_mem_periodicPts hy
  have hsucc : ∀ j, φ.perm^[m]^[j] y ∈ G.successors x := by
    intro j
    apply (G.mem_successors _ _).mpr
    have hfix : φ.perm^[m * j] x = x := (isPeriodicPt_minimalPeriod φ.perm x).mul_const j
    simpa only [← iterate_mul, hfix] using G.arrow_iterate φ hxy (m * j)
  have hpred : ∀ j, φ.perm^[n]^[j] x ∈ G.predecessors y := by
    intro j
    apply (G.mem_predecessors _ _).mpr
    have hfix : φ.perm^[n * j] y = y := (isPeriodicPt_minimalPeriod φ.perm y).mul_const j
    simpa only [← iterate_mul, hfix] using G.arrow_iterate φ hxy (n * j)
  have h₁ := (G.orbit_weight_le φ m y (G.successors x) hsucc).trans (G.successor_bound x)
  have h₂ := (G.orbit_weight_le φ n x (G.predecessors y) hpred).trans (G.predecessor_bound y)
  rw [period_of_power _ _ m hm] at h₁
  rw [period_of_power _ _ n hn, Nat.gcd_comm n m] at h₂
  have hproduct := Nat.mul_le_mul h₁ h₂
  have hwx := G.weight_pos x
  have hwy := G.weight_pos y
  change (m / Nat.gcd m n) * (n / Nat.gcd m n) ≤ G.bound ^ 2
  have hproduct' :
      ((m / Nat.gcd m n) * (n / Nat.gcd m n)) * (G.weight x * G.weight y) ≤
        G.bound ^ 2 * (G.weight x * G.weight y) := by
    simpa only [m, n, pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hproduct
  exact Nat.le_of_mul_le_mul_right hproduct' (Nat.mul_pos hwx hwy)

theorem adjacent_period_bound {x y : V} (hxy : G.underlyingGraph.Adj x y)
    (hx : x ∈ periodicPts φ.perm) (hy : y ∈ periodicPts φ.perm) :
    (minimalPeriod φ.perm x / Nat.gcd (minimalPeriod φ.perm x) (minimalPeriod φ.perm y)) *
      (minimalPeriod φ.perm y / Nat.gcd (minimalPeriod φ.perm x) (minimalPeriod φ.perm y)) ≤
      G.bound ^ 2 := by
  rcases hxy.2 with h | h
  · exact G.adjacent_period_bound_of_arrow φ h hx hy
  · simpa only [Nat.gcd_comm, Nat.mul_comm] using
      G.adjacent_period_bound_of_arrow φ h hy hx

/-- Manuscript Proposition `prop:prime-invariant`. -/
theorem prime_dvd_period_iff_of_reachable {x y : V}
    (hxy : G.underlyingGraph.Reachable x y) (hx : x ∈ periodicPts φ.perm)
    (p : ℕ) (hp : Nat.Prime p) (hlarge : G.bound ^ 2 < p) :
    (p ∣ minimalPeriod φ.perm x ↔ p ∣ minimalPeriod φ.perm y) := by
  obtain ⟨path⟩ := hxy
  induction path with
  | nil => rfl
  | @cons x z y h path ih =>
    have hz := G.periodic_of_adjacent φ h hx
    have heq := prime_dvd_iff_of_adjacent_bound
      (minimalPeriod φ.perm x) (minimalPeriod φ.perm z) G.bound p
      (minimalPeriod_pos_of_mem_periodicPts hx) (minimalPeriod_pos_of_mem_periodicPts hz)
      hp hlarge (G.adjacent_period_bound φ h hx hz)
    exact heq.trans (ih hz)

/-- The graph-theoretic separation used in `cor:module-periods`. -/
theorem not_reachable_of_prime_period_and_fixed {x y : V} (p : ℕ) (hp : Nat.Prime p)
    (hlarge : G.bound ^ 2 < p) (hx : minimalPeriod φ.perm x = p)
    (hy : φ.perm y = y) : ¬G.underlyingGraph.Reachable x y := by
  intro hxy
  have hxper : x ∈ periodicPts φ.perm :=
    minimalPeriod_pos_iff_mem_periodicPts.mp (hx ▸ hp.pos)
  have hyperiod : minimalPeriod φ.perm y = 1 :=
    minimalPeriod_eq_one_iff_isFixedPt.mpr hy
  have h := (G.prime_dvd_period_iff_of_reachable φ hxy hxper p hp hlarge).mp
    (hx ▸ dvd_refl p)
  rw [hyperiod] at h
  exact hp.not_dvd_one h

end WeightedDigraph
end C3PerfectField
