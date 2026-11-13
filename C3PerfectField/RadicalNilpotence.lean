module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! Manuscript external input `ext:nilpotence`, proved using Mathlib. -/

@[expose] public section

namespace C3PerfectField

universe u v

theorem jacobson_isNilpotent (k : Type u) (A : Type v)
    [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] :
    IsNilpotent (Ideal.jacobson (⊥ : Ideal A)) := by
  let : IsArtinianRing A := isArtinian_of_tower k (inferInstance : IsArtinian k A)
  exact IsArtinianRing.isNilpotent_jacobson_bot

/-- The radical is two-sided and has a zero positive power. -/
theorem jacobson_nilpotence (k : Type u) (A : Type v)
    [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A] :
    (Ideal.jacobson (⊥ : Ideal A)).IsTwoSided ∧
      ∃ n : ℕ, 0 < n ∧ Ideal.jacobson (⊥ : Ideal A) ^ n = ⊥ := by
  refine ⟨inferInstance, ?_⟩
  obtain ⟨n, hn⟩ := jacobson_isNilpotent k A
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  change Ideal.jacobson (⊥ : Ideal A) ^ n = ⊥ at hn
  rw [Submodule.pow_succ, hn, Ideal.bot_mul]

end C3PerfectField
