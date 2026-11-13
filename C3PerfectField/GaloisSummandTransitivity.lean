module

public import C3PerfectField.SummandClassProjections
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
The Galois orbit argument of manuscript `lem:transitivity`.
Orbit projections use actual indecomposable isomorphism classes and the
canonical semisimple endomorphism quotient, independently of a choice
of matrix-block coordinates.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat TensorProduct Classical

universe u v

variable {k K : Type u} {A : Type v}
  [Field k] [Field K] [Algebra k K] [Ring A] [Algebra k A]

theorem scalarExtensionAlgebraAut_refl :
    scalarExtensionAlgebraAut (A := A) (AlgEquiv.refl : K ≃ₐ[k] K) =
      AlgEquiv.refl := by
  ext z
  induction z using TensorProduct.inductionOn with
  | tmul c a => simp
  | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'

theorem scalarExtensionAlgebraAut_trans (σ τ : K ≃ₐ[k] K) :
    scalarExtensionAlgebraAut (A := A) (τ.trans σ) =
      (scalarExtensionAlgebraAut τ).trans (scalarExtensionAlgebraAut σ) := by
  ext z
  induction z using TensorProduct.inductionOn with
  | tmul c a => simp
  | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'

theorem scalarExtensionAlgebraAut_symm (σ : K ≃ₐ[k] K) :
    scalarExtensionAlgebraAut (A := A) σ.symm =
      (scalarExtensionAlgebraAut σ).symm := by
  ext z
  apply (scalarExtensionAlgebraAut σ).injective
  simp only [AlgEquiv.apply_symm_apply]
  induction z using TensorProduct.inductionOn with
  | tmul c a => simp
  | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'

/-- The actual coefficient twist on the extended algebra's AR vertices. -/
def arGaloisTwist (σ : K ≃ₐ[k] K) :
    ARVertex K (K ⊗[k] A) → ARVertex K (K ⊗[k] A) :=
  arTwist (scalarExtensionAlgebraAut_semilinear σ)

theorem arGaloisTwist_refl (x : ARVertex K (K ⊗[k] A)) :
    arGaloisTwist (AlgEquiv.refl : K ≃ₐ[k] K) x = x := by
  unfold arGaloisTwist
  have h : IsSemilinearAlgebraAut (RingEquiv.refl K)
      (RingEquiv.refl (K ⊗[k] A)) := fun _ => rfl
  convert arTwist_refl h x using 1
  congr 1
  exact congrArg AlgEquiv.toRingEquiv scalarExtensionAlgebraAut_refl

theorem arGaloisTwist_trans (σ τ : K ≃ₐ[k] K)
    (x : ARVertex K (K ⊗[k] A)) :
    arGaloisTwist σ (arGaloisTwist τ x) = arGaloisTwist (τ.trans σ) x := by
  unfold arGaloisTwist
  rw [arTwist_trans]
  congr 1
  exact congrArg AlgEquiv.toRingEquiv (scalarExtensionAlgebraAut_trans σ τ).symm

theorem arGaloisTwist_symm_apply (σ : K ≃ₐ[k] K)
    (x : ARVertex K (K ⊗[k] A)) :
    arGaloisTwist σ.symm (arGaloisTwist σ x) = x := by
  rw [arGaloisTwist_trans]
  simpa only [AlgEquiv.self_trans_symm] using arGaloisTwist_refl (k := k) x

/-- The orbit is a set of actual isomorphism classes, not a set of
decomposition indices or chosen representatives. -/
def arGaloisOrbit (x : ARVertex K (K ⊗[k] A)) : Set (ARVertex K (K ⊗[k] A)) :=
  {y | ∃ σ : K ≃ₐ[k] K, arGaloisTwist σ x = y}

theorem mem_arGaloisOrbit_self (x : ARVertex K (K ⊗[k] A)) :
    x ∈ arGaloisOrbit x :=
  ⟨AlgEquiv.refl, arGaloisTwist_refl x⟩

theorem arGaloisTwist_mem_orbit_iff (σ : K ≃ₐ[k] K)
    (x y : ARVertex K (K ⊗[k] A)) :
    arGaloisTwist σ y ∈ arGaloisOrbit x ↔ y ∈ arGaloisOrbit x := by
  have hforward (τ : K ≃ₐ[k] K) {y : ARVertex K (K ⊗[k] A)}
      (hy : y ∈ arGaloisOrbit x) : arGaloisTwist τ y ∈ arGaloisOrbit x := by
    obtain ⟨ρ, rfl⟩ := hy
    exact ⟨ρ.trans τ, (arGaloisTwist_trans τ ρ x).symm⟩
  constructor
  · intro hy
    simpa only [arGaloisTwist_symm_apply] using hforward σ.symm hy
  · exact hforward σ

/-- Transport a chosen decomposition through the actual fixed-twist
isomorphism and the functor's preserved biproduct. -/
def scalarExtensionTwistedDecomposition (σ : K ≃ₐ[k] K)
    (M : FiniteModule k A) {n : ℕ}
    (P : Fin n → IndecomposableModule K (K ⊗[k] A))
    (e : (scalarExtensionFiniteModule (L := K) M).val ≅ ⨁ fun i => (P i).obj) :
    (scalarExtensionFiniteModule (L := K) M).val ≅
      ⨁ fun i =>
        (twistIndecomposableModule (scalarExtensionAlgebraAut_semilinear σ) (P i)).obj :=
  (scalarExtensionTwistIso σ M.val).symm ≪≫
    (moduleTwist (scalarExtensionAlgebraAut (A := A) σ).toRingEquiv).mapIso e ≪≫
    (moduleTwist (scalarExtensionAlgebraAut (A := A) σ).toRingEquiv).mapBiproduct
      (fun i => (P i).obj)

theorem scalarExtensionTwistedDecomposition_inclusion (σ : K ≃ₐ[k] K)
    (M : FiniteModule k A) {n : ℕ}
    (P : Fin n → IndecomposableModule K (K ⊗[k] A))
    (e : (scalarExtensionFiniteModule (L := K) M).val ≅ ⨁ fun i => (P i).obj)
    (i : Fin n) :
    biproduct.ι (fun j =>
        (twistIndecomposableModule (scalarExtensionAlgebraAut_semilinear σ) (P j)).obj) i ≫
      (scalarExtensionTwistedDecomposition σ M P e).inv =
    (moduleTwist (scalarExtensionAlgebraAut (A := A) σ).toRingEquiv).map
      (biproduct.ι (fun j => (P j).obj) i ≫ e.inv) ≫
        (scalarExtensionTwistIso σ M.val).hom := by
  simp [scalarExtensionTwistedDecomposition, Category.assoc, Functor.map_comp]

/-- Conjugation carries a class-selected projection to the same selection
in the transported decomposition whenever the selection is twist invariant. -/
theorem scalarExtensionTwistConjugate_classProjection (σ : K ≃ₐ[k] K)
    (M : FiniteModule k A) {n : ℕ}
    (P : Fin n → IndecomposableModule K (K ⊗[k] A))
    (e : (scalarExtensionFiniteModule (L := K) M).val ≅ ⨁ fun i => (P i).obj)
    (S : Set (ARVertex K (K ⊗[k] A)))
    (hS : ∀ x, arGaloisTwist σ x ∈ S ↔ x ∈ S) :
    scalarExtensionTwistConjugate σ
        (summandClassProjectionHom (scalarExtensionFiniteModule (L := K) M) P e S) =
      summandClassProjectionHom (scalarExtensionFiniteModule (L := K) M)
        (fun i => twistIndecomposableModule
          (scalarExtensionAlgebraAut_semilinear σ) (P i))
        (scalarExtensionTwistedDecomposition σ M P e) S := by
  let Q := fun i => twistIndecomposableModule
    (scalarExtensionAlgebraAut_semilinear σ) (P i)
  let d := scalarExtensionTwistedDecomposition σ M P e
  let F := moduleTwist (scalarExtensionAlgebraAut (A := A) σ).toRingEquiv
  let t := scalarExtensionTwistIso σ M.val
  let p := summandClassProjectionHom (scalarExtensionFiniteModule (L := K) M) P e S
  apply (cancel_epi d.inv).mp
  apply biproduct.hom_ext'
  intro i
  let a := biproduct.ι (fun j => (P j).obj) i ≫ e.inv
  have hin : biproduct.ι (fun j => (Q j).obj) i ≫ d.inv = F.map a ≫ t.hom :=
    scalarExtensionTwistedDecomposition_inclusion σ M P e i
  have hmem : Quotient.mk _ (Q i) ∈ S ↔ Quotient.mk _ (P i) ∈ S :=
    hS (Quotient.mk _ (P i))
  have hpi : a ≫ p = if Quotient.mk _ (P i) ∈ S then a else 0 :=
    summandClassProjectionHom_inclusion _ P e S i
  rw [← Category.assoc, hin]
  change (F.map a ≫ t.hom) ≫ scalarExtensionTwistConjugate σ p =
    biproduct.ι (fun j => (Q j).obj) i ≫ d.inv ≫
      summandClassProjectionHom _ Q d S
  rw [← Category.assoc, summandClassProjectionHom_inclusion, hin]
  calc
    (F.map a ≫ t.hom) ≫ scalarExtensionTwistConjugate σ p =
        F.map (a ≫ p) ≫ t.hom := by
      simp [scalarExtensionTwistConjugate, F, t, Category.assoc, Functor.map_comp]
    _ = if Quotient.mk _ (P i) ∈ S then F.map a ≫ t.hom else 0 := by
      rw [hpi]
      split_ifs <;> simp
    _ = if Quotient.mk _ (Q i) ∈ S then F.map a ≫ t.hom else 0 := by
      rw [propext hmem]

variable [Module.Finite k A]

/-- The orbit projection is fixed in the actual semisimple End quotient.
Decomposition independence is what removes the choice of a decomposition. -/
theorem summandClassProjection_galois_fixed (σ : K ≃ₐ[k] K)
    (M : FiniteModule k A) {n : ℕ}
    (P : Fin n → IndecomposableModule K (K ⊗[k] A))
    (e : (scalarExtensionFiniteModule (L := K) M).val ≅ ⨁ fun i => (P i).obj)
    (x : ARVertex K (K ⊗[k] A)) :
    letI : Module.Finite k M.val := M.property
    moduleEndJacobsonQuotientGaloisAut M.val σ
        (summandClassProjection (scalarExtensionFiniteModule (L := K) M) P e
          (arGaloisOrbit x)) =
      summandClassProjection (scalarExtensionFiniteModule (L := K) M) P e
        (arGaloisOrbit x) := by
  let := M.property
  let p : End (scalarExtensionObject (k := k) (K := K) M.val) :=
    End.of (summandClassProjectionHom (scalarExtensionFiniteModule (L := K) M)
      P e (arGaloisOrbit x))
  change moduleEndJacobsonQuotientGaloisAut M.val σ (Ideal.Quotient.mk _ p) = _
  refine (moduleEndJacobsonQuotientGaloisAut_mk M.val σ p).trans ?_
  rw [moduleEndGaloisAut_eq_twistConjugate M.val σ p]
  change Ideal.Quotient.mk _
    (End.of (scalarExtensionTwistConjugate σ
      (summandClassProjectionHom (scalarExtensionFiniteModule (L := K) M) P e
        (arGaloisOrbit x)))) = _
  rw [scalarExtensionTwistConjugate_classProjection σ M P e (arGaloisOrbit x)
    (arGaloisTwist_mem_orbit_iff σ x)]
  exact (summandClassProjection_eq_of_decomposition
    (scalarExtensionFiniteModule (L := K) M) P e (arGaloisOrbit x)
    (fun i => twistIndecomposableModule (scalarExtensionAlgebraAut_semilinear σ) (P i))
    (scalarExtensionTwistedDecomposition σ M P e)).symm

variable [PerfectField k] [IsAlgClosure k K]

/-- The Galois group is transitive on the isomorphism classes occurring
in any indecomposable decomposition of an extended base indecomposable. -/
theorem exists_galois_twist_component_iso (X : IndecomposableModule k A)
    {n : ℕ} (P : Fin n → IndecomposableModule K (K ⊗[k] A))
    (e : (scalarExtensionFiniteModule (L := K) X.val).val ≅ ⨁ fun i => (P i).obj)
    (i j : Fin n) :
    ∃ σ : K ≃ₐ[k] K,
      Nonempty ((twistIndecomposableModule
        (scalarExtensionAlgebraAut_semilinear σ) (P i)).obj ≅ (P j).obj) := by
  let := X.val.property
  let W := scalarExtensionFiniteModule (L := K) X.val
  let x : ARVertex K (K ⊗[k] A) := Quotient.mk _ (P i)
  let S := arGaloisOrbit x
  let p := summandClassProjection W P e S
  have hi : Quotient.mk _ (P i) ∈ S := mem_arGaloisOrbit_self x
  have hj : Quotient.mk _ (P j) ∈ S := by
    by_contra hj
    have hp : IsIdempotentElem p := summandClassProjection_idempotent W P e S
    have hfix : ∀ σ : K ≃ₐ[k] K,
        moduleEndJacobsonQuotientGaloisAut X.obj σ p = p :=
      fun σ => summandClassProjection_galois_fixed σ X.val P e x
    rcases moduleEndJacobsonQuotient_twist_fixed_idempotent_eq_zero_or_one
      X hp hfix with hz | ho
    · exact summandClassProjection_ne_zero_of_mem W P e S i hi hz
    · exact summandClassProjection_ne_one_of_notMem W P e S j hj ho
  obtain ⟨σ, hσ⟩ := hj
  exact ⟨σ, Quotient.exact hσ⟩

/-- Manuscript `lem:transitivity`, for arbitrary actual indecomposable
summands of the extension of an original indecomposable. No transitivity,
matrix decomposition, or descent assumption is supplied. -/
theorem exists_galois_twist_iso_of_summands (X : IndecomposableModule k A)
    (U V : IndecomposableModule K (K ⊗[k] A))
    (hU : IsIndecomposableSummand U (scalarExtensionFiniteModule (L := K) X.val))
    (hV : IsIndecomposableSummand V (scalarExtensionFiniteModule (L := K) X.val)) :
    ∃ σ : K ≃ₐ[k] K,
      Nonempty ((twistIndecomposableModule
        (scalarExtensionAlgebraAut_semilinear σ) U).obj ≅ V.obj) := by
  obtain ⟨n, P, ⟨e⟩⟩ :=
    exists_indecomposable_biproduct (scalarExtensionFiniteModule (L := K) X.val)
  obtain ⟨i, ⟨ei⟩⟩ :=
    (isIndecomposableSummand_iff_component_iso U _ P e).mp hU
  obtain ⟨j, ⟨ej⟩⟩ :=
    (isIndecomposableSummand_iff_component_iso V _ P e).mp hV
  obtain ⟨σ, ⟨d⟩⟩ := exists_galois_twist_component_iso X P e i j
  exact ⟨σ, ⟨(moduleTwist (scalarExtensionAlgebraAut (A := A) σ).toRingEquiv).mapIso ei
    ≪≫ d ≪≫ ej.symm⟩⟩

end

end C3PerfectField
