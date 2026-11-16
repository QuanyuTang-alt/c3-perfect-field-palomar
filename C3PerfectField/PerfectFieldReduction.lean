module

public import C3PerfectField.ScalarExtensionComponents
public import C3PerfectField.AlgebraicallyClosedComponents
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
Conditional helpers for the polynomial-tensor route to the perfect-field result.
Their `PolynomialEmbeddingExistence` premise is explicit and is not discharged
in this file. They do not establish polynomial embedding existence.

The unconditional theorem `C3PerfectField.mainTheorem` is proved in
`C3Integration.lean`: it uses the proved Kronecker embedding and affine-cokernel
family together with the scalar-extension descent results imported here.
Importing this module does not add its conditional premises to that theorem.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open scoped ModuleCat TensorProduct Polynomial

universe u v

/-- Exact matrix-coordinate existence obligation corresponding to manuscript
`ext:embedding`. This is a proposition, not an axiom or a proved existence
theorem. Finite-free bimodule embeddings already give this proposition
by the checked coordinate-transport theorem. -/
def PolynomialEmbeddingExistence (k : Type u) (A : Type v)
    [Field k] [Ring A] [Algebra k A] : Prop :=
  InfiniteRepresentationType k A →
    ∃ (t : ℕ) (ρ : A →ₐ[k]
      Matrix (ULift.{max u v} (Fin t)) (ULift.{max u v} (Fin t)) k[X]),
        IsPolynomialRepresentationEmbedding ρ

variable {k K : Type u} {A : Type v}
  [Field k] [Field K] [Algebra k K] [Ring A] [Algebra k A]
  [Module.Finite k A] [PerfectField k] [IsAlgClosure k K]

/-- The polynomial-tensor route and the full component-descent theorem give
the target implication when the stated polynomial embedding existence premise
is supplied for the algebraic-closure extension. The unconditional affine route
is assembled separately in `C3Integration.lean`. -/
theorem mainStatement_of_scalarExtension_embeddingExistence
    (hB : PolynomialEmbeddingExistence K (K ⊗[k] A)) :
    MainStatement k A := by
  intro hA
  let : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  obtain ⟨t, ρ, hρ⟩ := hB (infiniteRepresentationType_scalarExtension hA)
  exact infinite_arComponents_of_scalarExtension
    (infinite_arComponents_of_polynomialRepresentationEmbedding ρ hρ)

omit [Field K] [Algebra k K] [IsAlgClosure k K] in
/-- The algebraic closure itself is constructed by Mathlib. This helper keeps
the polynomial embedding existence premise explicit. It is a conditional
reduction, not `C3PerfectField.mainTheorem` in `C3Integration.lean`. -/
theorem mainStatement_of_algebraicClosure_embeddingExistence
    (hB : PolynomialEmbeddingExistence (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A)) :
    MainStatement k A :=
  mainStatement_of_scalarExtension_embeddingExistence hB

end

end C3PerfectField
