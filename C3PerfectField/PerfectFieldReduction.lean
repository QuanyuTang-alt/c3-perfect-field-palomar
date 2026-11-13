module

public import C3PerfectField.ScalarExtensionComponents
public import C3PerfectField.AlgebraicallyClosedComponents
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
Assembly of the perfect-field argument, conditional on the outstanding
Bongartz representation-embedding existence theorem. The conditional
premise is explicit: this file does not prove `mainTheorem`.
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

/-- The closed-field argument and the full component-descent theorem
complete the target implication if the missing embedding theorem is
provided for the algebraic-closure extension. -/
theorem mainStatement_of_scalarExtension_embeddingExistence
    (hB : PolynomialEmbeddingExistence K (K ⊗[k] A)) :
    MainStatement k A := by
  intro hA
  let : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  obtain ⟨t, ρ, hρ⟩ := hB (infiniteRepresentationType_scalarExtension hA)
  exact infinite_arComponents_of_scalarExtension
    (infinite_arComponents_of_polynomialRepresentationEmbedding ρ hρ)

omit [Field K] [Algebra k K] [IsAlgClosure k K] in
/-- The algebraic closure itself is constructed by Mathlib. Its existence
adds no premise; only the unproved polynomial embedding existence remains.
This is a conditional reduction, not the unconditional main theorem. -/
theorem mainStatement_of_algebraicClosure_embeddingExistence
    (hB : PolynomialEmbeddingExistence (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A)) :
    MainStatement k A :=
  mainStatement_of_scalarExtension_embeddingExistence hB

end

end C3PerfectField
