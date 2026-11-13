module

public import C3PerfectField.SummandDescent

/-!
Manuscript `lem:radical-square`. The reverse inclusion uses the proved
summand descent for every finite intermediate A_K-module. Both sides
are the radical-square submodules from the literal finite-factorization
definition in the target statement.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace C3PerfectField

noncomputable section

open CategoryTheory
open scoped ModuleCat TensorProduct

universe u v

variable {k K : Type u} {A : Type v}
  [Field k] [Field K] [Algebra k K] [Ring A] [Algebra k A]

/-- Composition of two tensors of radical maps belongs to the tensor
extension of the actual radical square. -/
theorem moduleHomTensorComposition_mem_radicalSquare
    (M N P : ModuleCat.{max u v} A)
    {f : K ⊗[k] (M ⟶ N)} {g : K ⊗[k] (N ⟶ P)}
    [Module.Finite k N]
    (hf : f ∈ (radicalSubmodule (k := k) M N).baseChange K)
    (hg : g ∈ (radicalSubmodule (k := k) N P).baseChange K) :
    moduleHomTensorComposition M N P (f ⊗ₜ[K] g) ∈
      (radicalSquareSubmodule (k := k) M P).baseChange K := by
  obtain ⟨f, rfl⟩ := hf
  obtain ⟨g, rfl⟩ := hg
  induction f using TensorProduct.inductionOn with
  | tmul c f =>
    induction g using TensorProduct.inductionOn with
    | tmul d g =>
      simp only [LinearMap.baseChange_tmul, Submodule.subtype_apply,
        moduleHomTensorComposition_tmul]
      apply Submodule.tmul_mem_baseChange_of_mem
      refine ⟨1, fun _ => (⟨N, inferInstance⟩ : FiniteModule k A),
        fun _ => f.val, fun _ => g.val, fun _ => ⟨f.property, g.property⟩, ?_⟩
      simp
    | add g g' hg hg' =>
      simp only [map_add, TensorProduct.tmul_add]
      exact Submodule.add_mem _ hg hg'
  | add f f' hf hf' =>
    simp only [map_add, TensorProduct.add_tmul]
    exact Submodule.add_mem _ hf hf'

variable [Module.Finite k A] [PerfectField k] [IsAlgClosure k K]

/-- The actual scalar-extension functor takes radical maps to radical maps. -/
theorem IsRadical.scalarExtensionMap
    {M N : ModuleCat.{max u v} A} [Module.Finite k M] [Module.Finite k N]
    {f : M ⟶ N} (hf : IsRadical A f) :
    IsRadical.{u, max u v} (K ⊗[k] A)
      (scalarExtensionMap (k := k) (K := K) f) := by
  have h := (isRadical_moduleHomScalarExtensionEquiv_iff M N ((1 : K) ⊗ₜ[k] f)).mpr
    (Submodule.tmul_mem_baseChange_of_mem (1 : K) hf)
  simpa only [moduleHomScalarExtensionEquiv_tmul, one_smul] using h

/-- Extending a literal finite radical-factorization sum preserves membership. -/
theorem IsRadicalSquare.scalarExtensionMap
    {M N : ModuleCat.{max u v} A} [Module.Finite k M] [Module.Finite k N]
    {f : M ⟶ N} (hf : IsRadicalSquare k A f) :
    IsRadicalSquare K (K ⊗[k] A) (scalarExtensionMap (k := k) (K := K) f) := by
  classical
  obtain ⟨n, W, a, b, hab, rfl⟩ := hf
  let F := scalarExtensionFunctor (k := k) (K := K) (A := A)
  refine ⟨n, fun i => scalarExtensionFiniteModule (L := K) (W i),
    fun i => F.map (a i), fun i => F.map (b i), ?_, ?_⟩
  · intro i
    let := (W i).property
    exact ⟨(hab i).1.scalarExtensionMap, (hab i).2.scalarExtensionMap⟩
  · change F.map (∑ i, a i ≫ b i) = ∑ i, F.map (a i) ≫ F.map (b i)
    simp only [F.map_sum, F.map_comp]

/-- The reverse inclusion transfers an arbitrary finite intermediate module
into an extended base module using its actual splitting maps. -/
theorem mem_radicalSquare_baseChange_of_scalarExtension
    (M N : ModuleCat.{max u v} A) [Module.Finite k M] [Module.Finite k N]
    (z : K ⊗[k] (M ⟶ N))
    (hz : IsRadicalSquare K (K ⊗[k] A)
      (moduleHomScalarExtensionEquiv (k := k) (K := K) M N z)) :
    z ∈ (radicalSquareSubmodule (k := k) M N).baseChange K := by
  let : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  obtain ⟨T, a, b, ha, hb, hfac⟩ := hz.exists_radical_factorization
  obtain ⟨W, ⟨r⟩⟩ := exists_scalarExtension_retract T
  let := W.property
  let a' := a ≫ r.i
  let b' := r.r ≫ b
  let e := moduleHomScalarExtensionEquiv (k := k) (K := K) M N
  let e₁ := moduleHomScalarExtensionEquiv (k := k) (K := K) M W.val
  let e₂ := moduleHomScalarExtensionEquiv (k := k) (K := K) W.val N
  have ha' : e₁.symm a' ∈ (radicalSubmodule (k := k) M W.val).baseChange K :=
    (isRadical_moduleHomScalarExtensionEquiv_iff M W.val (e₁.symm a')).mp
      (by
        change IsRadical (K ⊗[k] A) (e₁ (e₁.symm a'))
        rw [e₁.apply_symm_apply]
        exact ha.postcomp r.i)
  have hb' : e₂.symm b' ∈ (radicalSubmodule (k := k) W.val N).baseChange K :=
    (isRadical_moduleHomScalarExtensionEquiv_iff W.val N (e₂.symm b')).mp
      (by
        change IsRadical (K ⊗[k] A) (e₂ (e₂.symm b'))
        rw [e₂.apply_symm_apply]
        exact hb.precomp r.r)
  have he : moduleHomTensorComposition M W.val N
      (e₁.symm a' ⊗ₜ[K] e₂.symm b') = z := by
    apply e.injective
    rw [moduleHomScalarExtensionEquiv_comp]
    change e₁ (e₁.symm a') ≫ e₂ (e₂.symm b') = e z
    rw [e₁.apply_symm_apply, e₂.apply_symm_apply]
    calc
      a' ≫ b' = a ≫ b := by
        dsimp only [a', b']
        rw [Category.assoc, ← Category.assoc r.i r.r b, r.retract,
          Category.id_comp]
      _ = e z := hfac.symm
  rw [← he]
  exact moduleHomTensorComposition_mem_radicalSquare M W.val N ha' hb'

/-- Elementwise manuscript `lem:radical-square`, with no extra descent premise. -/
theorem isRadicalSquare_moduleHomScalarExtensionEquiv_iff
    (M N : ModuleCat.{max u v} A) [Module.Finite k M] [Module.Finite k N]
    (z : K ⊗[k] (M ⟶ N)) :
    IsRadicalSquare K (K ⊗[k] A)
      (moduleHomScalarExtensionEquiv (k := k) (K := K) M N z) ↔
        z ∈ (radicalSquareSubmodule (k := k) M N).baseChange K := by
  constructor
  · exact mem_radicalSquare_baseChange_of_scalarExtension M N z
  · intro hz
    obtain ⟨x, rfl⟩ := hz
    induction x using TensorProduct.inductionOn with
    | tmul c f =>
      simp only [LinearMap.baseChange_tmul, Submodule.subtype_apply,
        moduleHomScalarExtensionEquiv_tmul]
      exact f.property.scalarExtensionMap.smul c
    | add x y hx hy =>
      simp only [map_add]
      exact hx.add hy

/-- The literal radical-square subspace equality under canonical Hom identification. -/
theorem algebraicClosure_radicalSquareSubmodule_scalarExtension
    (M N : ModuleCat.{max u v} A) [Module.Finite k M] [Module.Finite k N] :
    (radicalSquareSubmodule (k := K)
      (scalarExtensionObject (k := k) (K := K) M)
      (scalarExtensionObject (k := k) (K := K) N)).comap
        (moduleHomScalarExtensionEquiv (k := k) (K := K) M N).toLinearMap =
      (radicalSquareSubmodule (k := k) M N).baseChange K := by
  ext z
  exact isRadicalSquare_moduleHomScalarExtensionEquiv_iff M N z

/-- The displayed equality inside the extended Hom space. -/
theorem algebraicClosure_radicalSquareSubmodule_scalarExtension_map
    (M N : ModuleCat.{max u v} A) [Module.Finite k M] [Module.Finite k N] :
    ((radicalSquareSubmodule (k := k) M N).baseChange K).map
      (moduleHomScalarExtensionEquiv (k := k) (K := K) M N).toLinearMap =
        radicalSquareSubmodule (k := K)
          (scalarExtensionObject (k := k) (K := K) M)
          (scalarExtensionObject (k := k) (K := K) N) := by
  rw [← algebraicClosure_radicalSquareSubmodule_scalarExtension M N]
  exact Submodule.map_comap_eq_of_surjective
    (moduleHomScalarExtensionEquiv (k := k) (K := K) M N).surjective _

end

end C3PerfectField
