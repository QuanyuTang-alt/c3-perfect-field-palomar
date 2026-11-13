module

public import C3PerfectField.GaloisFixedField
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
Descent of invariant coordinate subspaces. A basis of the dual is selected
from the coordinate restrictions. Its dual basis has uniquely prescribed
coordinates, so invariance of the subspace fixes its basis vectors. This
proves the coordinate form of manuscript `lem:subspace-descent` without
assuming an echelon basis or a finite Galois extension.
-/

@[expose] public section

namespace C3PerfectField

noncomputable section

open Module

universe u v w

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
  {ι : Type w} [Finite ι]

/-- Any coordinate subspace has a basis whose coefficient maps are some
of the ambient coordinate restrictions. The selected coordinates determine
every vector in the subspace uniquely. -/
theorem exists_basis_coordinate_restrictions (W : Submodule K (ι → K)) :
    ∃ (η : Type (max v w)) (_ : Finite η) (b : Basis η K W) (p : η → ι),
      ∀ (x : W) (j : η), b.repr x j = x.val (p j) := by
  classical
  let L : ι → Dual K W := fun i => (LinearMap.proj i).comp W.subtype
  have hL : Submodule.span K (Set.range L) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro z hz
    have hzi : ∃ i, z.val i ≠ 0 := by
      by_contra h
      push Not at h
      apply hz
      apply Subtype.ext
      exact funext h
    obtain ⟨i, hi⟩ := hzi
    exact ⟨L i, ⟨i, rfl⟩, hi⟩
  let d := Basis.ofSpan hL.ge
  let η := (linearIndepOn_empty K id).extend (Set.empty_subset (Set.range L))
  let : Finite η := Module.Finite.finite_basis d
  let b : Basis η K W := d.dualBasis.map (Module.evalEquiv K W).symm
  have hd (j : η) : ∃ i, L i = d j :=
    Basis.ofSpan_subset hL.ge ⟨j, rfl⟩
  choose p hp using hd
  refine ⟨η, inferInstance, b, p, ?_⟩
  intro x j
  change d.dualBasis.repr ((Module.evalEquiv K W) x) j = _
  rw [Basis.dualBasis_repr]
  change d j x = x.val (p j)
  rw [← hp j]
  rfl

/-- Base-field vectors whose coordinate inclusion belongs to W. -/
def descendedCoordinateSubspace (W : Submodule K (ι → K)) : Submodule k (ι → k) :=
  (W.restrictScalars k).comap (coordinateScalarInclusion k K ι)

omit [Finite ι] in
@[simp]
theorem mem_descendedCoordinateSubspace (W : Submodule K (ι → K)) (x : ι → k) :
    x ∈ descendedCoordinateSubspace (k := k) W ↔ coordinateScalarInclusion k K ι x ∈ W :=
  Iff.rfl

/-- An invariant coordinate subspace is spanned over K by its vectors
defined over k. Only the stated fixed-scalar property of the subgroup is
required; the extension and subgroup need not be finite. -/
theorem coordinate_subspace_descent (G : Subgroup (K ≃ₐ[k] K))
    (hG : ∀ x : K, (∀ σ : G, σ.val x = x) → ∃ c : k, algebraMap k K c = x)
    (W : Submodule K (ι → K))
    (hW : ∀ (σ : G) (x : ι → K), x ∈ W → coordinateGaloisAction σ.val x ∈ W) :
    W = Submodule.span K
      (coordinateScalarInclusion k K ι ''
        (descendedCoordinateSubspace (k := k) W : Set (ι → k))) := by
  classical
  obtain ⟨η, hη, b, p, hb⟩ := exists_basis_coordinate_restrictions W
  let := hη
  have hfixed (i : η) (σ : G) :
      coordinateGaloisAction σ.val (b i).val = (b i).val := by
    let x : W := ⟨coordinateGaloisAction σ.val (b i).val, hW σ _ (b i).property⟩
    have hx : x = b i := by
      apply b.ext_elem
      intro j
      rw [hb x j, hb (b i) j]
      change σ.val ((b i).val (p j)) = (b i).val (p j)
      rw [← hb (b i) j, Basis.repr_self_apply]
      split_ifs <;> simp
    exact congrArg Subtype.val hx
  have hbdesc (i : η) :
      (b i).val ∈ coordinateScalarInclusion k K ι ''
        (descendedCoordinateSubspace (k := k) W : Set (ι → k)) := by
    obtain ⟨y, hy⟩ := (coordinate_fixed_iff G hG (b i).val).mp (hfixed i)
    refine ⟨y, ?_, hy⟩
    change coordinateScalarInclusion k K ι y ∈ W
    rw [hy]
    exact (b i).property
  apply le_antisymm
  · have hs : Submodule.span K (Set.range (fun i => (b i).val)) = W := by
      have h := congrArg (Submodule.map W.subtype) b.span_eq
      rw [Submodule.map_span, Submodule.map_subtype_top] at h
      simpa only [← Set.range_comp, Function.comp_def, Submodule.subtype_apply] using h
    calc
      W = Submodule.span K (Set.range (fun i => (b i).val)) := hs.symm
      _ ≤ _ := ?_
    exact Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact hbdesc i)
  · apply Submodule.span_le.mpr
    rintro _ ⟨y, hy, rfl⟩
    exact hy

/-- The coordinate descent theorem specialized to a perfect field and its
algebraic closure, without a fixed-field hypothesis as an extra premise. -/
theorem algebraicClosure_coordinate_subspace_descent [PerfectField k] [IsAlgClosure k K]
    (W : Submodule K (ι → K))
    (hW : ∀ (σ : K ≃ₐ[k] K) (x : ι → K), x ∈ W → coordinateGaloisAction σ x ∈ W) :
    W = Submodule.span K
      (coordinateScalarInclusion k K ι ''
        (descendedCoordinateSubspace (k := k) W : Set (ι → k))) := by
  apply coordinate_subspace_descent (⊤ : Subgroup (K ≃ₐ[k] K))
  · intro x hx
    exact (algebraicClosure_fixed_iff x).mp (fun σ => hx ⟨σ, trivial⟩)
  · intro σ x hx
    exact hW σ.val x hx

end

end C3PerfectField
