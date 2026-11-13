module

public import C3PerfectField.ScalarExtensionIrreducibleSpaces
public import C3PerfectField.ScalarExtensionFixedTwists

/-!
The block-existence step of manuscript `lem:edge-lift`. A nonzero
irreducible quotient of finite modules gives an arrow between some
indecomposable summands. Scalar extension preserves and reflects the
existence of such an arrow. Choosing a prescribed source summand still
requires the separate Galois-transitivity theorem.
-/

@[expose] public section

namespace C3PerfectField

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat TensorProduct

universe u v

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]

/-- The nonzero quotient criterion also applies to decomposable endpoints. -/
theorem nontrivial_irreducibleSpace_iff_exists
    (M N : ModuleCat.{max u v} A) :
    Nontrivial (IrreducibleSpace (k := k) M N) ↔
      ∃ f : M ⟶ N, IsRadical A f ∧ ¬IsRadicalSquare k A f := by
  change Nontrivial (radicalSubmodule (k := k) M N ⧸
    (radicalSquareSubmodule (k := k) M N).comap
      (radicalSubmodule (k := k) M N).subtype) ↔ _
  simp only [Submodule.Quotient.nontrivial_iff, ne_eq, Submodule.eq_top_iff']
  constructor
  · intro h
    classical
    push Not at h
    obtain ⟨⟨f, hf⟩, hf2⟩ := h
    exact ⟨f, hf, hf2⟩
  · rintro ⟨f, hf, hf2⟩ h
    exact hf2 (h ⟨f, hf⟩)

/-- Nonzero irreducible spaces between arbitrary finite modules are detected
by their actual indecomposable direct-summand blocks. -/
theorem nontrivial_irreducibleSpace_iff_exists_summand_arrow
    (M N : FiniteModule k A) :
    Nontrivial (IrreducibleSpace (k := k) M.val N.val) ↔
      ∃ U V : IndecomposableModule k A,
        IsIndecomposableSummand U M ∧ IsIndecomposableSummand V N ∧
          HasARArrow k A U V := by
  classical
  rw [nontrivial_irreducibleSpace_iff_exists]
  constructor
  · rintro ⟨f, hf, hf2⟩
    obtain ⟨n, P, ⟨e⟩⟩ := exists_indecomposable_biproduct M
    obtain ⟨m, Q, ⟨d⟩⟩ := exists_indecomposable_biproduct N
    let f' := e.inv ≫ f ≫ d.hom
    have hr : IsRadical A f' := (isRadical_iso_iff e.symm d f).mpr hf
    have hr2 : ¬IsRadicalSquare k A f' :=
      fun h => hf2 ((isRadicalSquare_iso_iff e.symm d f).mp h)
    have hblock : ∃ i j, ¬IsRadicalSquare k A
        (biproduct.ι (fun a => (P a).obj) i ≫ f' ≫
          biproduct.π (fun b => (Q b).obj) j) := by
      by_contra h
      push Not at h
      exact hr2 ((isRadicalSquare_iff_blocks _ _ f').mpr h)
    obtain ⟨i, j, hij⟩ := hblock
    refine ⟨P i, Q j, ?_, ?_, ?_⟩
    · exact (isIndecomposableSummand_iff_component_iso (P i) M P e).mpr
        ⟨i, ⟨Iso.refl _⟩⟩
    · exact (isIndecomposableSummand_iff_component_iso (Q j) N Q d).mpr
        ⟨j, ⟨Iso.refl _⟩⟩
    · exact ⟨_, (isRadical_iff_blocks _ _ f').mp hr i j, hij⟩
  · rintro ⟨U, V, ⟨i, p, hip⟩, ⟨j, q, hjq⟩, f, hf, hf2⟩
    refine ⟨p ≫ f ≫ j, (hf.precomp p).postcomp j, ?_⟩
    intro h
    have h' := (h.precomp i).postcomp q
    have he : i ≫ (p ≫ f ≫ j) ≫ q = f := by
      simp only [← Category.assoc, hip, Category.id_comp]
      rw [Category.assoc, hjq, Category.comp_id]
    exact hf2 (he ▸ h')

variable {K : Type u} [Field K] [Algebra k K]
  [Module.Finite k A] [PerfectField k] [IsAlgClosure k K]

/-- A base-field arrow lifts to an arrow between some actual extended
indecomposable summands, and any such arrow reflects to the base field. -/
theorem hasARArrow_iff_scalarExtension_summand_arrow
    (X Y : IndecomposableModule k A) :
    HasARArrow k A X Y ↔
      ∃ U V : IndecomposableModule K (K ⊗[k] A),
        IsIndecomposableSummand U (scalarExtensionFiniteModule (L := K) X.val) ∧
        IsIndecomposableSummand V (scalarExtensionFiniteModule (L := K) Y.val) ∧
          HasARArrow K (K ⊗[k] A) U V := by
  let := X.val.property
  let := Y.val.property
  rw [hasARArrow_iff_nontrivial_irreducibleSpace,
    ← nontrivial_irreducibleSpace_scalarExtension_iff (K := K) X.obj Y.obj]
  exact nontrivial_irreducibleSpace_iff_exists_summand_arrow
    (scalarExtensionFiniteModule (L := K) X.val)
    (scalarExtensionFiniteModule (L := K) Y.val)

end

end C3PerfectField
