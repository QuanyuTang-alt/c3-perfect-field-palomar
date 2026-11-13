-- Ported for the pinned Lean/Mathlib version with Doubao assistance; original notices retained.
module

public import C3PerfectField.Radicals
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
Finite direct-sum block compatibility from manuscript Lemma `lem:radical-ideal`.
These lemmas use the actual module biproducts and the target's radical-square
definition; no matrix-block hypothesis is added to the main statement.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat BigOperators

universe u v w w'

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

/-- The off-diagonal matrix identifies the radical with its Jacobson corner. -/
theorem isRadical_iff_corner_mem_jacobson
    {X Y : ModuleCat.{max u v} A} (f : X ⟶ Y) :
    IsRadical A f ↔
      End.of (biprod.fst ≫ f ≫ biprod.inr : X ⊞ Y ⟶ X ⊞ Y) ∈
        Ideal.jacobson (⊥ : Ideal (End (X ⊞ Y))) := by
  rw [← isRadical_end_iff_mem_jacobson]
  constructor
  · intro h
    exact (h.postcomp biprod.inr).precomp biprod.fst
  · intro h
    simpa using (h.precomp biprod.inl).postcomp biprod.snd

variable {ι : Type w} {κ : Type w'}
    [Fintype ι] [Fintype κ]
    (U : ι → ModuleCat.{max u v} A) (V : κ → ModuleCat.{max u v} A)
    [HasBiproduct U] [HasBiproduct V]

/-- Recover a map from its finite direct-sum blocks. -/
theorem hom_eq_sum_blocks (f : ⨁ U ⟶ ⨁ V) :
    f = ∑ i, ∑ j,
      biproduct.π U i ≫ (biproduct.ι U i ≫ f ≫ biproduct.π V j) ≫ biproduct.ι V j := by
  calc
    f = (∑ i, biproduct.π U i ≫ biproduct.ι U i) ≫ f ≫
        (∑ j, biproduct.π V j ≫ biproduct.ι V j) := by
      have hU : (∑ i, biproduct.π U i ≫ biproduct.ι U i) = 𝟙 (⨁ U) := by
        classical
        apply biproduct.hom_ext
        intro i
        rw [Preadditive.sum_comp, Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          rw [Category.assoc, biproduct.ι_π_ne U hji, comp_zero]
        · simp
      have hV : (∑ j, biproduct.π V j ≫ biproduct.ι V j) = 𝟙 (⨁ V) := by
        classical
        apply biproduct.hom_ext
        intro j
        rw [Preadditive.sum_comp, Finset.sum_eq_single j]
        · simp
        · intro i _ hij
          rw [Category.assoc, biproduct.ι_π_ne V hij, comp_zero]
        · simp
      rw [hU, hV, Category.id_comp, Category.comp_id]
    _ = _ := by
      simp only [Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
      rw [Finset.sum_comm]

theorem isRadical_iff_blocks (f : ⨁ U ⟶ ⨁ V) :
    IsRadical A f ↔
      ∀ i j, IsRadical A (biproduct.ι U i ≫ f ≫ biproduct.π V j) := by
  constructor
  · intro h i j
    exact (h.postcomp (biproduct.π V j)).precomp (biproduct.ι U i)
  · intro h
    rw [hom_eq_sum_blocks U V f]
    apply isRadical_sum Finset.univ
    intro i _
    apply isRadical_sum Finset.univ
    intro j _
    exact ((h i j).postcomp (biproduct.ι V j)).precomp (biproduct.π U i)

theorem isRadicalSquare_iff_blocks (f : ⨁ U ⟶ ⨁ V) :
    IsRadicalSquare k A f ↔
      ∀ i j, IsRadicalSquare k A (biproduct.ι U i ≫ f ≫ biproduct.π V j) := by
  constructor
  · intro h i j
    exact (h.postcomp (biproduct.π V j)).precomp (biproduct.ι U i)
  · intro h
    rw [hom_eq_sum_blocks U V f]
    apply isRadicalSquare_sum Finset.univ
    intro i _
    apply isRadicalSquare_sum Finset.univ
    intro j _
    exact ((h i j).postcomp (biproduct.ι V j)).precomp (biproduct.π U i)

end C3PerfectField
