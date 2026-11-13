module

public import C3PerfectField.GaloisSummandTransitivity
public import C3PerfectField.ScalarExtensionArrowBlocks

/-!
Manuscript `lem:edge-lift` and `lem:path-lift` on the actual AR quivers.
An arrow can be lifted from either a prescribed source or a prescribed
target summand. Connectivity is then lifted along actual graph walks.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open CategoryTheory
open scoped ModuleCat TensorProduct

universe u v

variable {k K : Type u} {A : Type v}
  [Field k] [Field K] [Algebra k K] [Ring A] [Algebra k A]
  [Module.Finite k A] [PerfectField k] [IsAlgClosure k K]

/-- Lift a directed arrow from any prescribed summand of its source. -/
theorem exists_scalarExtension_arrow_from_summand
    (X Y : IndecomposableModule k A) (hXY : HasARArrow k A X Y)
    (U : IndecomposableModule K (K ⊗[k] A))
    (hU : IsIndecomposableSummand U (scalarExtensionFiniteModule (L := K) X.val)) :
    ∃ V : IndecomposableModule K (K ⊗[k] A),
      IsIndecomposableSummand V (scalarExtensionFiniteModule (L := K) Y.val) ∧
        HasARArrow K (K ⊗[k] A) U V := by
  obtain ⟨P, Q, hP, hQ, hPQ⟩ :=
    (hasARArrow_iff_scalarExtension_summand_arrow (K := K) X Y).mp hXY
  obtain ⟨σ, ⟨e⟩⟩ := exists_galois_twist_iso_of_summands X P U hP hU
  let hσ := scalarExtensionAlgebraAut_semilinear (A := A) σ
  exact ⟨twistIndecomposableModule hσ Q,
    isIndecomposableSummand_scalarExtension_twist σ Y.val Q hQ,
    (hasARArrow_iso_iff e (Iso.refl _)).mp
      ((hasARArrow_twist_iff hσ P Q).mpr hPQ)⟩

/-- Lift a directed arrow to any prescribed summand of its target. -/
theorem exists_scalarExtension_arrow_to_summand
    (X Y : IndecomposableModule k A) (hYX : HasARArrow k A Y X)
    (U : IndecomposableModule K (K ⊗[k] A))
    (hU : IsIndecomposableSummand U (scalarExtensionFiniteModule (L := K) X.val)) :
    ∃ V : IndecomposableModule K (K ⊗[k] A),
      IsIndecomposableSummand V (scalarExtensionFiniteModule (L := K) Y.val) ∧
        HasARArrow K (K ⊗[k] A) V U := by
  obtain ⟨Q, P, hQ, hP, hQP⟩ :=
    (hasARArrow_iff_scalarExtension_summand_arrow (K := K) Y X).mp hYX
  obtain ⟨σ, ⟨e⟩⟩ := exists_galois_twist_iso_of_summands X P U hP hU
  let hσ := scalarExtensionAlgebraAut_semilinear (A := A) σ
  exact ⟨twistIndecomposableModule hσ Q,
    isIndecomposableSummand_scalarExtension_twist σ Y.val Q hQ,
    (hasARArrow_iso_iff (Iso.refl _) e).mp
      ((hasARArrow_twist_iff hσ Q P).mpr hQP)⟩

/-- A directed edge, including a loop, gives undirected connectivity. -/
theorem arGraph_reachable_of_arrow_or_reverse
    {F : Type*} {B : Type*} [Field F] [Ring B] [Algebra F B]
    {x y : ARVertex F B} (h : ARArrow F B x y ∨ ARArrow F B y x) :
    (ARGraph F B).Reachable x y := by
  by_cases hxy : x = y
  · subst y
    exact SimpleGraph.Reachable.rfl
  · exact SimpleGraph.Adj.reachable (G := ARGraph F B) ⟨hxy, h⟩

/-- Lift one undirected edge from its prescribed initial summand. -/
theorem exists_scalarExtension_edge_from_summand
    (X Y : IndecomposableModule k A)
    (hXY : HasARArrow k A X Y ∨ HasARArrow k A Y X)
    (U : IndecomposableModule K (K ⊗[k] A))
    (hU : IsIndecomposableSummand U (scalarExtensionFiniteModule (L := K) X.val)) :
    ∃ V : IndecomposableModule K (K ⊗[k] A),
      IsIndecomposableSummand V (scalarExtensionFiniteModule (L := K) Y.val) ∧
        (ARGraph K (K ⊗[k] A)).Reachable (Quotient.mk _ U) (Quotient.mk _ V) := by
  rcases hXY with hXY | hYX
  · obtain ⟨V, hV, hUV⟩ := exists_scalarExtension_arrow_from_summand X Y hXY U hU
    exact ⟨V, hV, arGraph_reachable_of_arrow_or_reverse
      (Or.inl ((arArrow_mk_iff U V).mpr hUV))⟩
  · obtain ⟨V, hV, hVU⟩ := exists_scalarExtension_arrow_to_summand X Y hYX U hU
    exact ⟨V, hV, arGraph_reachable_of_arrow_or_reverse
      (Or.inr ((arArrow_mk_iff V U).mpr hVU))⟩

/-- Lift actual base-quiver connectivity from any prescribed extended
summand of the initial vertex. All intermediate summands are obtained
successively by the edge-lifting theorem. -/
theorem exists_scalarExtension_path_from_summand
    {x y : ARVertex k A} (hxy : (ARGraph k A).Reachable x y)
    (U : IndecomposableModule K (K ⊗[k] A))
    (hU : IsIndecomposableSummand U (scalarExtensionFiniteModule (L := K) x.out.val)) :
    ∃ V : IndecomposableModule K (K ⊗[k] A),
      IsIndecomposableSummand V (scalarExtensionFiniteModule (L := K) y.out.val) ∧
        (ARGraph K (K ⊗[k] A)).Reachable (Quotient.mk _ U) (Quotient.mk _ V) := by
  obtain ⟨w⟩ := hxy
  induction w generalizing U with
  | nil => exact ⟨U, hU, SimpleGraph.Reachable.rfl⟩
  | @cons x z y hxz w ih =>
    have harrow : HasARArrow k A x.out z.out ∨ HasARArrow k A z.out x.out := by
      have h := hxz.2
      rw [← Quotient.out_eq x, ← Quotient.out_eq z] at h
      simpa only [arArrow_mk_iff] using h
    obtain ⟨V, hV, hUV⟩ := exists_scalarExtension_edge_from_summand x.out z.out harrow U hU
    obtain ⟨W, hW, hVW⟩ := ih V hV
    exact ⟨W, hW, hUV.trans hVW⟩

/-- The same path-lifting result with arbitrary endpoint representatives,
rather than the quotient's chosen representatives. -/
theorem exists_scalarExtension_path_of_reachable
    (X Y : IndecomposableModule k A)
    (hXY : (ARGraph k A).Reachable (Quotient.mk _ X) (Quotient.mk _ Y))
    (U : IndecomposableModule K (K ⊗[k] A))
    (hU : IsIndecomposableSummand U (scalarExtensionFiniteModule (L := K) X.val)) :
    ∃ V : IndecomposableModule K (K ⊗[k] A),
      IsIndecomposableSummand V (scalarExtensionFiniteModule (L := K) Y.val) ∧
        (ARGraph K (K ⊗[k] A)).Reachable (Quotient.mk _ U) (Quotient.mk _ V) := by
  let F := scalarExtensionFunctor (k := k) (K := K) (A := A)
  let x : ARVertex k A := Quotient.mk _ X
  let y : ARVertex k A := Quotient.mk _ Y
  obtain ⟨ex⟩ : Nonempty (x.out.obj ≅ X.obj) := Quotient.exact (Quotient.out_eq x)
  obtain ⟨ey⟩ : Nonempty (y.out.obj ≅ Y.obj) := Quotient.exact (Quotient.out_eq y)
  have hx : IsIndecomposableSummand U
      (scalarExtensionFiniteModule (L := K) x.out.val) :=
    (isIndecomposableSummand_iff_of_iso U (F.mapIso ex)).mpr hU
  obtain ⟨V, hV, hUV⟩ := exists_scalarExtension_path_from_summand hXY U hx
  exact ⟨V, (isIndecomposableSummand_iff_of_iso V (F.mapIso ey)).mp hV, hUV⟩

end

end C3PerfectField
