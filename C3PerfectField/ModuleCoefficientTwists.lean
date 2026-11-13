module

public import C3PerfectField.BasisCoefficientAutomorphisms
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
The finite-module-list part of manuscript Lemma `lem:coefficient-field`.
Fixed action coefficients give an explicit module isomorphism from each
twist, by applying the field automorphism to the module coordinates.
The polynomial family and its equivariance are separate remaining steps.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open CategoryTheory
open scoped BigOperators ModuleCat

universe u v w z

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]
  {ι : Type w} [Fintype ι] {κ : Type z} [Fintype κ]

/-- Actual action-matrix coefficients in chosen finite bases. -/
def moduleBasisCoefficients (bA : Module.Basis ι k A) (U : ModuleCat.{max u v} A)
    (bU : Module.Basis κ k U) : Finset k := by
  classical
  exact Finset.univ.image (fun ijr : ι × κ × κ => bU.repr (bA ijr.1 • bU ijr.2.1) ijr.2.2)

theorem fixes_moduleBasisCoefficients (bA : Module.Basis ι k A)
    (U : ModuleCat.{max u v} A) (bU : Module.Basis κ k U) (σ : k ≃+* k)
    (h : ∀ c ∈ moduleBasisCoefficients bA U bU, σ c = c) :
    ∀ i j r, σ (bU.repr (bA i • bU j) r) = bU.repr (bA i • bU j) r := by
  classical
  intro i j r
  apply h
  unfold moduleBasisCoefficients
  exact Finset.mem_image.mpr ⟨(i, j, r), Finset.mem_univ _, rfl⟩

/-- Coordinate conjugation intertwines the full algebra action, rather
than only its values on the chosen basis vectors. -/
theorem basisCoordinateAut_action (bA : Module.Basis ι k A)
    (U : ModuleCat.{max u v} A) (bU : Module.Basis κ k U) (σ : k ≃+* k)
    (h : ∀ i j r, σ (bU.repr (bA i • bU j) r) = bU.repr (bA i • bU j) r)
    (a : A) (x : U) :
    basisCoordinateAut bU σ (a • x) =
      basisCoordinateAut bA σ a • basisCoordinateAut bU σ x := by
  have hp (i : ι) (j : κ) :
      basisCoordinateAut bU σ (bA i • bU j) = bA i • bU j :=
    basisCoordinateAut_fixed bU σ _ (h i j)
  have hx (i : ι) : basisCoordinateAut bU σ (bA i • x) =
      bA i • basisCoordinateAut bU σ x := by
    conv_lhs => rw [← bU.sum_repr x, Finset.smul_sum]
    rw [map_sum]
    conv_rhs => rw [← bU.sum_repr x, map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_comm (bA i), basisCoordinateAut_smul, hp,
      basisCoordinateAut_smul, smul_comm (bA i), basisCoordinateAut_basis]
  conv_lhs => rw [← bA.sum_repr a, Finset.sum_smul]
  rw [map_sum]
  conv_rhs => rw [← bA.sum_repr a, map_sum, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_assoc, basisCoordinateAut_smul, hx, basisCoordinateAut_smul,
    smul_assoc, basisCoordinateAut_basis]

/-- The same σ-coordinate map is A-linear from the inverse-action twist. -/
def moduleBasisTwistIso (bA : Module.Basis ι k A)
    (U : ModuleCat.{max u v} A) (bU : Module.Basis κ k U) (σ : k ≃+* k)
    (h1 : ∀ i, σ (bA.repr 1 i) = bA.repr 1 i)
    (hm : ∀ i j r, σ (bA.repr (bA i * bA j) r) = bA.repr (bA i * bA j) r)
    (hU : ∀ i j r, σ (bU.repr (bA i • bU j) r) = bU.repr (bA i • bU j) r) :
    (moduleTwist (basisAlgebraAut bA σ h1 hm)).obj U ≅ U := by
  let α := basisAlgebraAut bA σ h1 hm
  let γ : U ≃+ U := basisCoordinateAut bU σ
  let e : (moduleTwist α).obj U ≃ₗ[A] U := {
    toAddEquiv := γ
    map_smul' := fun a x => by
      change basisCoordinateAut bU σ (α.symm a • (show U from x)) =
        a • basisCoordinateAut bU σ (show U from x)
      rw [basisCoordinateAut_action bA U bU σ hU]
      change α (α.symm a) • basisCoordinateAut bU σ (show U from x) = _
      rw [α.apply_symm_apply]
  }
  exact e.toModuleIso

/-- A coefficient field supplying the actual algebra automorphism and the
fixed-module isomorphism for every automorphism fixing that entire field. -/
theorem exists_coefficientField_fixed_module (bA : Module.Basis ι k A)
    (U : ModuleCat.{max u v} A) (bU : Module.Basis κ k U) :
    ∃ F : Subfield k, Field.FG F ∧
      ∀ σ : k ≃ₐ[F] k, ∃ α : A ≃+* A,
        IsSemilinearAlgebraAut σ.toRingEquiv α ∧ Nonempty ((moduleTwist α).obj U ≅ U) := by
  classical
  let S := algebraBasisCoefficients bA ∪ moduleBasisCoefficients bA U bU
  let F := coefficientField S
  refine ⟨F, coefficientField_fg S, ?_⟩
  intro σ
  have hfix (c : k) (hc : c ∈ S) : σ c = c := by
    exact σ.commutes ⟨c, mem_coefficientField hc⟩
  obtain ⟨h1, hm⟩ := fixes_algebraBasisCoefficients bA σ.toRingEquiv
    (fun c hc => hfix c (Finset.mem_union_left _ hc))
  have hU := fixes_moduleBasisCoefficients bA U bU σ.toRingEquiv
    (fun c hc => hfix c (Finset.mem_union_right _ hc))
  exact ⟨basisAlgebraAut bA σ.toRingEquiv h1 hm,
    basisAlgebraAut_semilinear bA σ.toRingEquiv h1 hm,
    ⟨moduleBasisTwistIso bA U bU σ.toRingEquiv h1 hm hU⟩⟩

/-- The common action with its coordinate formula exposed, so that a polynomial
family can use precisely the same algebra automorphisms as the finite list. -/
theorem exists_coefficientField_basisModuleAction (bA : Module.Basis ι k A)
    {η : Type z} [Finite η] (U : η → FiniteModule k A) (S : Finset k) :
    ∃ F : Subfield k, Field.FG F ∧ (∀ c ∈ S, c ∈ F) ∧
      ∃ α : (k ≃ₐ[F] k) → (A ≃+* A),
        (∀ σ a, α σ a = basisCoordinateAut bA σ.toRingEquiv a) ∧
        (∀ σ, IsSemilinearAlgebraAut σ.toRingEquiv (α σ)) ∧
        α (AlgEquiv.refl : k ≃ₐ[F] k) = RingEquiv.refl A ∧
        (∀ σ τ, α (τ.trans σ) = (α τ).trans (α σ)) ∧
        ∀ σ j, Nonempty ((moduleTwist (α σ)).obj (U j).val ≅ (U j).val) := by
  classical
  let := Fintype.ofFinite η
  have hUfin (j : η) : Module.Finite k (U j).val := (U j).property
  let bU (j : η) : Module.Basis (Fin (Module.finrank k (U j).val)) k (U j).val := by
    letI := hUfin j
    exact Module.finBasis k (U j).val
  let T := algebraBasisCoefficients bA ∪
    (S ∪ Finset.univ.biUnion (fun j => moduleBasisCoefficients bA (U j).val (bU j)))
  let F := coefficientField T
  have hS (c : k) (hc : c ∈ S) : c ∈ F :=
    mem_coefficientField (Finset.mem_union_right _
      (Finset.mem_union_left _ hc))
  have hfix (σ : k ≃ₐ[F] k) (c : k) (hc : c ∈ T) : σ c = c :=
    σ.commutes ⟨c, mem_coefficientField hc⟩
  have hA (σ : k ≃ₐ[F] k) :
      (∀ i, σ (bA.repr 1 i) = bA.repr 1 i) ∧
        ∀ i j r, σ (bA.repr (bA i * bA j) r) = bA.repr (bA i * bA j) r :=
    fixes_algebraBasisCoefficients bA σ.toRingEquiv
      (fun c hc => hfix σ c (Finset.mem_union_left _ hc))
  let α (σ : k ≃ₐ[F] k) := basisAlgebraAut bA σ.toRingEquiv (hA σ).1 (hA σ).2
  refine ⟨F, coefficientField_fg T, hS, α, fun _ _ => rfl,
    fun σ => basisAlgebraAut_semilinear bA σ.toRingEquiv (hA σ).1 (hA σ).2,
    ?_, ?_, ?_⟩
  · apply RingEquiv.ext
    intro a
    change basisCoordinateAut bA (AlgEquiv.refl : k ≃ₐ[F] k).toRingEquiv a = a
    exact basisCoordinateAut_fixed bA _ a (fun _ => rfl)
  · intro σ τ
    apply RingEquiv.ext
    intro a
    change basisCoordinateAut bA (τ.trans σ).toRingEquiv a =
      basisCoordinateAut bA σ.toRingEquiv (basisCoordinateAut bA τ.toRingEquiv a)
    apply bA.repr.injective
    ext i
    simp
  · intro σ j
    have hQ := fixes_moduleBasisCoefficients bA (U j).val (bU j) σ.toRingEquiv
      (fun c hc => hfix σ c (Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hc⟩))))
    exact ⟨moduleBasisTwistIso bA (U j).val (bU j) σ.toRingEquiv (hA σ).1 (hA σ).2 hQ⟩

/-- A common coefficient field for any finite list of actual finite modules,
with a compatible action of the full group of field automorphisms. Additional
finitely many coefficients can be included for the polynomial family. -/
theorem exists_coefficientField_moduleAction [FiniteDimensional k A]
    {η : Type z} [Finite η] (U : η → FiniteModule k A) (S : Finset k) :
    ∃ F : Subfield k, Field.FG F ∧ (∀ c ∈ S, c ∈ F) ∧
      ∃ α : (k ≃ₐ[F] k) → (A ≃+* A),
        (∀ σ, IsSemilinearAlgebraAut σ.toRingEquiv (α σ)) ∧
        α (AlgEquiv.refl : k ≃ₐ[F] k) = RingEquiv.refl A ∧
        (∀ σ τ, α (τ.trans σ) = (α τ).trans (α σ)) ∧
        ∀ σ j, Nonempty ((moduleTwist (α σ)).obj (U j).val ≅ (U j).val) := by
  obtain ⟨F, hF, hS, α, _, hα, hid, hcomp, hU⟩ :=
    exists_coefficientField_basisModuleAction (Module.finBasis k A) U S
  exact ⟨F, hF, hS, α, hα, hid, hcomp, hU⟩

end

end C3PerfectField
