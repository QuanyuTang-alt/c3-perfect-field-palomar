module

public import C3PerfectField.AlgebraicallyClosedComponents
public import C3PerfectField.MorphismCoefficientTwists
public import Mathlib.Algebra.Category.ModuleCat.Kernels

/-!
An actual affine cokernel family suffices for infinitely many AR components.
Unlike polynomial matrix transport, this accepts a literal family presented
by two fixed finite modules and two fixed morphisms. Family existence remains
an obligation for the arbitrary representation-infinite main theorem.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace C3PerfectField
noncomputable section
open CategoryTheory Limits Function
open scoped ModuleCat
universe u v
variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]
  {P Q : ModuleCat.{max u v} A}

/-- A quotient of a genuine finite module has finite canonical field action. -/
theorem finite_cokernel [Module.Finite k Q] (f : P ⟶ Q) :
    Module.Finite k (↑(cokernel f)) := by
  let p : Q →ₗ[k] ↑(cokernel f) := (cokernel.π f).hom.restrictScalars k
  have hp : Function.Surjective p :=
    (ModuleCat.epi_iff_surjective (cokernel.π f)).mp inferInstance
  exact Module.Finite.of_surjective p hp

/-- The actual isomorphism class of an indecomposable affine cokernel. -/
def affineCokernelVertex [Module.Finite k Q] (f g : P ⟶ Q)
    (hind : ∀ lambda : k, Indecomposable (cokernel (f - lambda • g)))
    (lambda : k) : ARVertex k A :=
  Quotient.mk _ ⟨⟨cokernel (f - lambda • g), finite_cokernel _⟩, hind lambda⟩

theorem affineCokernelVertex_injective [Module.Finite k Q] (f g : P ⟶ Q)
    (hind : ∀ lambda : k, Indecomposable (cokernel (f - lambda • g)))
    (hreflect : ∀ lambda mu : k,
      Nonempty (cokernel (f - lambda • g) ≅ cokernel (f - mu • g)) → lambda = mu) :
    Function.Injective (affineCokernelVertex f g hind) := by
  intro lambda mu h
  exact hreflect lambda mu (Quotient.exact h)

/-- A genuine affine cokernel family with parameter reflection has infinitely
many components. Its hypotheses do not constitute an unconditional main proof. -/
theorem infinite_arComponents_of_injective_affineCokernelFamily
    [FiniteDimensional k A] [IsAlgClosed k] [Module.Finite k P] [Module.Finite k Q]
    (f g : P ⟶ Q)
    (hind : ∀ lambda : k, Indecomposable (cokernel (f - lambda • g)))
    (hreflect : ∀ lambda mu : k,
      Nonempty (cokernel (f - lambda • g) ≅ cokernel (f - mu • g)) → lambda = mu) :
    Infinite (ARGraph k A).ConnectedComponent := by
  classical
  let G := arWeightedDigraph (k := k) (A := A)
  change Infinite G.underlyingGraph.ConnectedComponent
  apply G.infinite_components_of_prime_period_witness
  intro s
  let U : s → FiniteModule k A := fun y => y.val.out.val
  obtain ⟨F, hF, α, hα, hU, hfamily⟩ :=
    exists_coefficientField_affineCokernelAction U f g
  let := hF
  obtain ⟨p, σ, lambda, hp, hlarge, hperiod⟩ := exists_large_prime_period F (G.bound ^ 2)
  let φ : G.Automorphism := arWeightedTwist (hα σ)
  have hequiv (mu : k) :
      φ.perm (affineCokernelVertex f g hind mu) = affineCokernelVertex f g hind (σ mu) := by
    apply Quotient.sound
    exact hfamily σ mu
  refine ⟨φ, p, affineCokernelVertex f g hind lambda, hp, hlarge, ?_, ?_⟩
  · exact (minimalPeriod_of_injective_semiconj (affineCokernelVertex f g hind) σ φ.perm
      (affineCokernelVertex_injective f g hind hreflect) hequiv lambda).trans hperiod
  · intro y hy
    let j : s := ⟨y, hy⟩
    have hout : Quotient.mk _ y.out = y := Quotient.out_eq y
    rw [← hout]
    apply Quotient.sound
    exact hU σ j

end
end C3PerfectField
