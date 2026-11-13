module

public import C3PerfectField.ModuleCoefficientTwists
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
Coordinate conjugation for actual morphisms of finite modules. A finite list
of coefficients controls an entire affine pencil f - lambda g; consequently
its genuine cokernels move equivariantly under field automorphisms.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace C3PerfectField
noncomputable section
open CategoryTheory Limits
open scoped BigOperators ModuleCat
universe u v w z
variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]
  {ι : Type w} [Fintype ι] {κ : Type z} [Fintype κ]
  {P Q : ModuleCat.{max u v} A}

/-- The finite matrix-coefficient set of a genuine module morphism. -/
def morphismBasisCoefficients (bP : Module.Basis ι k P) (bQ : Module.Basis κ k Q)
    (f : P ⟶ Q) : Finset k := by
  classical
  exact Finset.univ.image (fun ij : ι × κ => bQ.repr (f (bP ij.1)) ij.2)

theorem fixes_morphismBasisCoefficients (bP : Module.Basis ι k P)
    (bQ : Module.Basis κ k Q) (f : P ⟶ Q) (σ : k ≃+* k)
    (h : ∀ c ∈ morphismBasisCoefficients bP bQ f, σ c = c) :
    ∀ i j, σ (bQ.repr (f (bP i)) j) = bQ.repr (f (bP i)) j := by
  classical
  intro i j
  exact h _ (Finset.mem_image.mpr ⟨(i,j), Finset.mem_univ _, rfl⟩)

omit [Fintype κ] in
/-- Fixed morphism coefficients give literal coordinate conjugation, not just
an abstract existence of an isomorphism. -/
theorem basisCoordinateAut_morphism (bP : Module.Basis ι k P)
    (bQ : Module.Basis κ k Q) (f : P ⟶ Q) (σ : k ≃+* k)
    (h : ∀ i j, σ (bQ.repr (f (bP i)) j) = bQ.repr (f (bP i)) j) (x : P) :
    basisCoordinateAut bQ σ (f x) = f (basisCoordinateAut bP σ x) := by
  have hb (i : ι) : basisCoordinateAut bQ σ (f (bP i)) = f (bP i) :=
    basisCoordinateAut_fixed bQ σ _ (h i)
  conv_lhs => rw [← bP.sum_repr x, map_sum]
  rw [map_sum]
  conv_rhs => rw [← bP.sum_repr x, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hlin (c : k) (y : P) : f (c • y) = c • f y :=
    (f.hom.restrictScalars k).map_smul c y
  simp only [hlin, basisCoordinateAut_smul, hb, basisCoordinateAut_basis]

omit [Fintype κ] in
/-- The parameter is moved by the field automorphism in the literal affine map. -/
theorem basisCoordinateAut_affine (bP : Module.Basis ι k P)
    (bQ : Module.Basis κ k Q) (f g : P ⟶ Q) (σ : k ≃+* k)
    (hf : ∀ i j, σ (bQ.repr (f (bP i)) j) = bQ.repr (f (bP i)) j)
    (hg : ∀ i j, σ (bQ.repr (g (bP i)) j) = bQ.repr (g (bP i)) j)
    (lambda : k) (x : P) :
    basisCoordinateAut bQ σ ((f - lambda • g) x) =
      (f - σ lambda • g) (basisCoordinateAut bP σ x) := by
  change basisCoordinateAut bQ σ (f x - lambda • g x) =
    f (basisCoordinateAut bP σ x) - σ lambda • g (basisCoordinateAut bP σ x)
  rw [map_sub, basisCoordinateAut_smul, basisCoordinateAut_morphism bP bQ f σ hf,
    basisCoordinateAut_morphism bP bQ g σ hg]

/-- Coordinate conjugation induces the actual isomorphism of cokernels. -/
def affineCokernelTwistIso {δ : Type w} [Fintype δ]
    (bA : Module.Basis δ k A) (bP : Module.Basis ι k P)
    (bQ : Module.Basis κ k Q) (f g : P ⟶ Q) (σ : k ≃+* k)
    (h1 : ∀ i, σ (bA.repr 1 i) = bA.repr 1 i)
    (hm : ∀ i j r, σ (bA.repr (bA i * bA j) r) = bA.repr (bA i * bA j) r)
    (hP : ∀ i j r, σ (bP.repr (bA i • bP j) r) = bP.repr (bA i • bP j) r)
    (hQ : ∀ i j r, σ (bQ.repr (bA i • bQ j) r) = bQ.repr (bA i • bQ j) r)
    (hf : ∀ i j, σ (bQ.repr (f (bP i)) j) = bQ.repr (f (bP i)) j)
    (hg : ∀ i j, σ (bQ.repr (g (bP i)) j) = bQ.repr (g (bP i)) j)
    (lambda : k) :
    (moduleTwist (basisAlgebraAut bA σ h1 hm)).obj (cokernel (f - lambda • g)) ≅
      cokernel (f - σ lambda • g) := by
  let α := basisAlgebraAut bA σ h1 hm
  let eP := moduleBasisTwistIso bA P bP σ h1 hm hP
  let eQ := moduleBasisTwistIso bA Q bQ σ h1 hm hQ
  have hsquare : (moduleTwist α).map (f - lambda • g) ≫ eQ.hom =
      eP.hom ≫ (f - σ lambda • g) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change basisCoordinateAut bQ σ ((f - lambda • g) (show P from x)) =
      (f - σ lambda • g) (basisCoordinateAut bP σ (show P from x))
    exact basisCoordinateAut_affine bP bQ f g σ hf hg (lambda := lambda) (show P from x)
  exact PreservesCokernel.iso (moduleTwist α) (f - lambda • g) ≪≫
    cokernel.mapIso ((moduleTwist α).map (f - lambda • g))
      (f - σ lambda • g) eP eQ hsquare

/-- A single finitely generated coefficient field fixes a finite module list
and moves every cokernel in the actual affine pencil. -/
theorem exists_coefficientField_affineCokernelAction [FiniteDimensional k A]
    [Module.Finite k P] [Module.Finite k Q]
    {η : Type z} [Finite η] (U : η → FiniteModule k A) (f g : P ⟶ Q) :
    ∃ F : Subfield k, Field.FG F ∧
      ∃ α : (k ≃ₐ[F] k) → (A ≃+* A),
        (∀ σ, IsSemilinearAlgebraAut σ.toRingEquiv (α σ)) ∧
        (∀ σ j, Nonempty ((moduleTwist (α σ)).obj (U j).val ≅ (U j).val)) ∧
        ∀ σ lambda, Nonempty ((moduleTwist (α σ)).obj (cokernel (f - lambda • g)) ≅
          cokernel (f - σ lambda • g)) := by
  classical
  let bA := Module.finBasis k A
  let bP := Module.finBasis k P
  let bQ := Module.finBasis k Q
  let S := algebraBasisCoefficients bA ∪ (moduleBasisCoefficients bA P bP ∪
    (moduleBasisCoefficients bA Q bQ ∪ (morphismBasisCoefficients bP bQ f ∪
      morphismBasisCoefficients bP bQ g)))
  obtain ⟨F, hF, hS, α, hcoord, hα, _, _, hU⟩ :=
    exists_coefficientField_basisModuleAction bA U S
  refine ⟨F, hF, α, hα, hU, ?_⟩
  intro σ lambda
  have hfix (c : k) (hc : c ∈ S) : σ c = c := σ.commutes ⟨c, hS c hc⟩
  obtain ⟨h1, hm⟩ := fixes_algebraBasisCoefficients bA σ.toRingEquiv
    (fun c hc => hfix c (Finset.mem_union_left _ hc))
  have hP := fixes_moduleBasisCoefficients bA P bP σ.toRingEquiv
    (fun c hc => hfix c (Finset.mem_union_right _ (Finset.mem_union_left _ hc)))
  have hQ := fixes_moduleBasisCoefficients bA Q bQ σ.toRingEquiv
    (fun c hc => hfix c (Finset.mem_union_right _
      (Finset.mem_union_right _ (Finset.mem_union_left _ hc))))
  have hf := fixes_morphismBasisCoefficients bP bQ f σ.toRingEquiv
    (fun c hc => hfix c (Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_union_right _ (Finset.mem_union_left _ hc)))))
  have hg := fixes_morphismBasisCoefficients bP bQ g σ.toRingEquiv
    (fun c hc => hfix c (Finset.mem_union_right _ (Finset.mem_union_right _
      (Finset.mem_union_right _ (Finset.mem_union_right _ hc)))))
  have heq : α σ = basisAlgebraAut bA σ.toRingEquiv h1 hm := RingEquiv.ext (hcoord σ)
  rw [heq]
  exact ⟨affineCokernelTwistIso bA bP bQ f g σ.toRingEquiv h1 hm hP hQ hf hg lambda⟩

end
end C3PerfectField
