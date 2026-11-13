module

public import LargeIndecomposable.KroneckerModules.Basic

/-!
Actual one-parameter regular Kronecker modules, constructed independently for
connecting the Bongartz embedding to the C3 manuscript. This is not a theorem
about Auslander--Reiten components and does not assume that the parameter
family exists: the family is defined by the literal arrow maps 1 and lambda.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace C3Kronecker

open CategoryTheory Limits
open LargeIndecomposable LargeIndecomposable.Statement
open WalkingParallelPair

universe u
variable {k : Type u} [Field k]

/-- The actual regular module (k,k;1,lambda). -/
abbrev regular (lambda : k) : D k :=
  ⟨Kron.mk (ModuleCat.of k k) (ModuleCat.of k k) (𝟙 _)
    (ModuleCat.ofHom (lambda • LinearMap.id)), by
    rw [inD_iff]
    intro v hv _
    exact hv⟩

/-- The two components of a regular-module morphism agree. -/
theorem regular_hom_components {lambda mu : k}
    (f : regular lambda ⟶ regular mu) :
    f.hom.app zero = f.hom.app one := by
  have h := Kron.a_comp f.hom
  change (𝟙 (ModuleCat.of k k)) ≫
    (f.hom.app one : ModuleCat.of k k ⟶ ModuleCat.of k k) =
    (f.hom.app zero : ModuleCat.of k k ⟶ ModuleCat.of k k) ≫ (𝟙 (ModuleCat.of k k)) at h
  change (f.hom.app zero : ModuleCat.of k k ⟶ ModuleCat.of k k) =
    (f.hom.app one : ModuleCat.of k k ⟶ ModuleCat.of k k)
  exact (Category.comp_id _).symm.trans (h.symm.trans (Category.id_comp _))

/-- Every regular-module endomorphism is scalar multiplication. -/
theorem regular_end_scalar (lambda : k) (f : regular lambda ⟶ regular lambda) :
    ∃ c : k, ∀ j : WalkingParallelPair, (f.hom.app j).hom = c • LinearMap.id := by
  let c : k := (f.hom.app zero).hom (1 : k)
  let g : k →ₗ[k] k := (f.hom.app zero).hom
  have hg : g = c • (LinearMap.id : k →ₗ[k] k) := by
    apply LinearMap.ext
    intro (x : k)
    change g x = c * x
    calc
      g x = x • g (1 : k) := by
        rw [← map_smul]; simp only [smul_eq_mul, mul_one]
      _ = c * x := mul_comm x c
  have hz : (f.hom.app zero).hom = c • (LinearMap.id : k →ₗ[k] k) := hg
  refine ⟨c, fun j => ?_⟩
  cases j with
  | zero => exact hz
  | one => rw [← regular_hom_components f]; exact hz

/-- The literal regular family consists of indecomposables. -/
theorem regular_indecomposable (lambda : k) : IsIndecomposableKron (regular lambda) := by
  constructor
  · intro hz
    have h := congrArg (fun f : (regular lambda).obj ⟶ (regular lambda).obj =>
      (f.app zero).hom (1 : k)) ((IsZero.iff_id_eq_zero _).mp hz)
    change (1 : k) = 0 at h
    exact one_ne_zero h
  · intro e he
    obtain ⟨c, hc⟩ := regular_end_scalar lambda e
    have hs : c * c = c := by
      have h := congrArg (fun f : regular lambda ⟶ regular lambda =>
        (f.hom.app zero).hom (1 : k)) he
      change (e.hom.app zero).hom ((e.hom.app zero).hom (1 : k)) =
        (e.hom.app zero).hom (1 : k) at h
      simpa only [hc, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul,
        mul_one] using h
    have hprod : c * (c - 1) = 0 := by rw [mul_sub, mul_one, hs, sub_self]
    rcases mul_eq_zero.mp hprod with h0 | h1
    · left
      apply ObjectProperty.hom_ext _
      apply Kron.hom_ext
      · apply ModuleCat.hom_ext
        rw [hc, h0, zero_smul]
        rfl
      · apply ModuleCat.hom_ext
        rw [hc, h0, zero_smul]
        rfl
    · right
      have hc1 : c = 1 := sub_eq_zero.mp h1
      apply ObjectProperty.hom_ext _
      apply Kron.hom_ext
      · apply ModuleCat.hom_ext
        rw [hc, hc1, one_smul]
        rfl
      · apply ModuleCat.hom_ext
        rw [hc, hc1, one_smul]
        rfl

/-- Isomorphism of actual regular modules forces parameter equality. -/
theorem regular_iso_parameter {lambda mu : k}
    (e : regular lambda ≅ regular mu) : lambda = mu := by
  let c : k := (e.hom.hom.app zero).hom (1 : k)
  have h0 : c ≠ 0 := by
    intro hc
    have h := congrArg (fun f : (regular lambda).obj ⟶ (regular lambda).obj =>
      (f.app zero).hom (1 : k)) (ObjectProperty.isoHom_inv_id_hom e)
    have hn : (e.hom.hom.app zero).hom (1 : k) = 0 := hc
    have hv : (e.inv.hom.app zero).hom ((e.hom.hom.app zero).hom (1 : k)) = (1 : k) := by
      change (e.inv.hom.app zero).hom ((e.hom.hom.app zero).hom (1 : k)) = (1 : k) at h
      exact h
    rw [hn, map_zero] at hv
    exact (zero_ne_one : (0 : k) ≠ 1) hv
  have hp := Kron.b_apply e.hom.hom (1 : k)
  have heq := regular_hom_components e.hom
  have hmul : lambda * c = mu * c := by
    let g : k →ₗ[k] k := (e.hom.hom.app zero).hom
    let h : k →ₗ[k] k := (e.hom.hom.app one).hom
    have hg : g = h := congrArg ModuleCat.Hom.hom heq
    have hp0 : h (lambda • (1 : k)) = mu • g (1 : k) := hp
    rw [← hg, map_smul] at hp0
    exact hp0
  exact mul_right_cancel₀ h0 hmul

/-- The regular modules are genuinely finite-dimensional at both vertices. -/
theorem regular_finite (lambda : k) : (regular lambda).obj.IsFiniteDimensional := by
  change FiniteDimensional k k ∧ FiniteDimensional k k
  exact ⟨inferInstance, inferInstance⟩

end C3Kronecker
