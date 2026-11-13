module

public import C3PerfectField.WeightedGraph

/-!
The final finite-component contradiction in the algebraically closed argument,
as a graph lemma. Its witness hypothesis must still be constructed for the
actual module category; it is not part of the manuscript's main statement.
-/

@[expose] public section

namespace C3PerfectField

universe u
variable {V : Type u}

/-- If every finite collection of vertices misses a connected component,
there are infinitely many components. -/
theorem infinite_components_of_finite_set_separation (G : SimpleGraph V)
    (hsep : ∀ s : Finset V, ∃ x : V, ∀ y ∈ s, ¬G.Reachable x y) :
    Infinite G.ConnectedComponent := by
  classical
  by_contra h
  let : Finite G.ConnectedComponent := not_infinite_iff_finite.mp h
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have hex : ∀ c : G.ConnectedComponent, ∃ y, G.connectedComponentMk y = c := by
    intro c
    exact c.ind (fun y => ⟨y, rfl⟩)
  choose rep hrep using hex
  obtain ⟨x, hx⟩ := hsep (Finset.univ.image rep)
  let c := G.connectedComponentMk x
  have hmem : rep c ∈ Finset.univ.image rep :=
    Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩
  exact hx (rep c) hmem (SimpleGraph.ConnectedComponent.exact (hrep c).symm)

/-- Graph part of manuscript Theorem `thm:closed`: prime-period witnesses
separating every finite set of fixed vertices force infinitely many components.

The witness condition is an explicit hypothesis of this standalone graph
lemma. Proving it from infinite representation type is still an obligation. -/
theorem WeightedDigraph.infinite_components_of_prime_period_witness
    (G : WeightedDigraph V)
    (hwitness : ∀ s : Finset V, ∃ (φ : G.Automorphism) (p : ℕ) (x : V),
      Nat.Prime p ∧ G.bound ^ 2 < p ∧ Function.minimalPeriod φ.perm x = p ∧
        ∀ y ∈ s, φ.perm y = y) :
    Infinite G.underlyingGraph.ConnectedComponent := by
  apply infinite_components_of_finite_set_separation
  intro s
  obtain ⟨φ, p, x, hp, hlarge, hx, hfixed⟩ := hwitness s
  exact ⟨x, fun y hy =>
    G.not_reachable_of_prime_period_and_fixed φ p hp hlarge hx (hfixed y hy)⟩

end C3PerfectField
