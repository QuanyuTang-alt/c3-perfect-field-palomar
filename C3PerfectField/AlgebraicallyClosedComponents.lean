module

public import C3PerfectField.PolynomialRepresentationEmbeddings
public import C3PerfectField.ARTwisting
public import C3PerfectField.PrimeCoefficientOrbits
public import C3PerfectField.ComponentSeparation

/-!
The algebraically closed component argument for a supplied polynomial tensor
representation embedding. This helper proves a conditional statement; it does
not construct the polynomial embedding from infinite representation type.
Its tensor modules and AR graph are the actual representation-theoretic objects.

The unconditional algebraically closed result and perfect-field main theorem
are proved in `C3Integration.lean` using the proved Kronecker embedding and the
affine-cokernel family from `AffineCokernelComponents.lean`. The stronger
polynomial-tensor existence predicate is not a premise of those final theorems.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open CategoryTheory Function
open scoped ModuleCat Polynomial

universe u v w z

/-- An injective equivariant parameterization preserves exact periods. -/
theorem minimalPeriod_of_injective_semiconj
    {X : Type w} {Y : Type z} (i : X → Y) (f : X → X) (g : Y → Y)
    (hi : Function.Injective i) (h : ∀ x, g (i x) = i (f x)) (x : X) :
    Function.minimalPeriod g (i x) = Function.minimalPeriod f x := by
  have hn (n : ℕ) : g^[n] (i x) = i (f^[n] x) := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, h,
        Function.iterate_succ_apply']
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro n
  change g^[n] (i x) = i x ↔ f^[n] x = x
  rw [hn]
  exact hi.eq_iff

variable {k : Type u} {A : Type v} [Field k] [Ring A] [Algebra k A]
  [FiniteDimensional k A] [IsAlgClosed k]
  {κ : Type (max u v)} [Fintype κ] [DecidableEq κ]

/-- A supplied genuine tensor representation embedding yields infinitely many
actual AR components. Polynomial embedding existence is not proved by this
helper. For the unconditional result, see
`infinite_arComponents_algebraicallyClosed` in `C3Integration.lean`. -/
theorem infinite_arComponents_of_polynomialRepresentationEmbedding
    (ρ : A →ₐ[k] Matrix κ κ k[X]) (hρ : IsPolynomialRepresentationEmbedding ρ) :
    Infinite (ARGraph k A).ConnectedComponent := by
  classical
  let G := arWeightedDigraph (k := k) (A := A)
  change Infinite G.underlyingGraph.ConnectedComponent
  apply G.infinite_components_of_prime_period_witness
  intro s
  let U : s → FiniteModule k A := fun y => y.val.out.val
  obtain ⟨F, hF, _, α, hα, _, _, hU, hfamily⟩ :=
    exists_coefficientField_polynomialTensorAction U ρ ∅
  let := hF
  obtain ⟨p, σ, lambda, hp, hlarge, hperiod⟩ := exists_large_prime_period F (G.bound ^ 2)
  let φ : G.Automorphism := arWeightedTwist (hα σ)
  have hequiv (mu : k) :
      φ.perm (hρ.familyVertex mu) = hρ.familyVertex (σ mu) := by
    apply Quotient.sound
    exact hfamily σ mu
  refine ⟨φ, p, hρ.familyVertex lambda, hp, hlarge, ?_, ?_⟩
  · exact (minimalPeriod_of_injective_semiconj hρ.familyVertex σ φ.perm
      hρ.familyVertex_injective hequiv lambda).trans hperiod
  · intro y hy
    let j : s := ⟨y, hy⟩
    have hout : Quotient.mk _ y.out = y := Quotient.out_eq y
    rw [← hout]
    apply Quotient.sound
    exact hU σ j

end

end C3PerfectField
