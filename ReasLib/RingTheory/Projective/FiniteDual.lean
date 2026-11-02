/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import ReasLib.RingTheory.Projective.NotLocallyFree

@[expose] public section

namespace PrefixOnes

/-- The prefix-ones ideal is not finitely generated over the product ring `ℕ → ZMod 2`. -/
theorem not_finite : ¬ Module.Finite (ℕ → ZMod 2) ideal := by
  classical
  intro h
  have hfg : (Submodule.span (ℕ → ZMod 2) (Set.range seq)).FG :=
    Module.Finite.iff_fg.mp h
  obtain ⟨s, hs, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (Set.range seq)).mp hfg
  -- A finite collection of prefixes vanishes beyond a common bound.
  have hbound : ∀ t : Finset (ℕ → ZMod 2), (↑t : Set (ℕ → ZMod 2)) ⊆ Set.range seq →
      ∃ n, ∀ x ∈ t, ∀ i, n ≤ i → x i = 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact fun _ ↦ ⟨0, by simp⟩
    | @insert x t hx ih =>
      intro ht
      obtain ⟨m, rfl⟩ := ht (Finset.mem_insert_self x t)
      obtain ⟨n, hn⟩ := ih (fun y hy ↦ ht (Finset.mem_insert_of_mem hy))
      refine ⟨max m n, ?_⟩
      intro y hy i hi
      rcases Finset.mem_insert.mp hy with rfl | hy
      · simp [seq, Nat.not_lt.mpr (le_trans (le_max_left m n) hi)]
      · exact hn y hy i (le_trans (le_max_right m n) hi)
  obtain ⟨n, hn⟩ := hbound s hs
  have hzero : ∀ x ∈ Submodule.span (ℕ → ZMod 2) (↑s : Set (ℕ → ZMod 2)), x n = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hn x hx n le_rfl
    | zero => rfl
    | add x y _ _ hx hy => change x n + y n = 0; rw [hx, hy, add_zero]
    | smul a x _ hx => change a n * x n = 0; rw [hx, mul_zero]
  have hseq : seq (n + 1) ∈ Submodule.span (ℕ → ZMod 2) (↑s : Set (ℕ → ZMod 2)) := by
    rw [← hspan]
    exact Submodule.subset_span ⟨n + 1, rfl⟩
  have hcontra : (1 : ZMod 2) = 0 := by simpa [seq] using hzero _ hseq
  exact one_ne_zero hcontra

/-- Consecutive prefix-ones differences `seq (n + 1) - seq n` lie in the prefix-ones ideal. -/
theorem coord_mem (n : ℕ) : seq (n + 1) - seq n ∈ ideal :=
  ideal.sub_mem (Ideal.subset_span ⟨n + 1, rfl⟩) (Ideal.subset_span ⟨n, rfl⟩)

/-- The standard prefix difference `seq (n + 1) - seq n` in the prefix-ones ideal, supported at `n`. -/
def coord (n : ℕ) : ideal :=
  ⟨seq (n + 1) - seq n, coord_mem n⟩

/-- The underlying sequence of `coord n` is the consecutive prefix-ones difference. -/
theorem coord_apply (n : ℕ) : (coord n : ℕ → ZMod 2) = seq (n + 1) - seq n := rfl

private theorem coord_apply_index (n i : ℕ) :
    (coord n : ℕ → ZMod 2) i = if i = n then 1 else 0 := by
  by_cases h : i = n
  · subst i
    simp [coord, seq]
  · by_cases hi : i < n
    · simp only [coord, seq, Pi.sub_apply, if_pos (Nat.lt_succ_of_lt hi), if_pos hi,
        sub_self, if_neg h]
    · have hnot : ¬ i < n + 1 := by
        intro hlt
        exact h (Nat.le_antisymm (Nat.le_of_lt_succ hlt) (Nat.le_of_not_gt hi))
      simp only [coord, seq, Pi.sub_apply, if_neg hnot, if_neg hi, sub_self, if_neg h]

/-- Left multiplication by an element of `ℕ → ZMod 2`, restricted along the inclusion of
the prefix-ones ideal, as a map into the dual module. -/
def selfToDual :
    (ℕ → ZMod 2) →ₗ[ℕ → ZMod 2] Module.Dual (ℕ → ZMod 2) ideal :=
  LinearMap.lcomp (ℕ → ZMod 2) (ℕ → ZMod 2) (Submodule.subtype ideal) ∘ₗ
    LinearMap.mul (ℕ → ZMod 2) (ℕ → ZMod 2)

/-- `selfToDual r` acts on the prefix-ones ideal by multiplication by `r`. -/
theorem selfToDual_apply (r : ℕ → ZMod 2) (x : ideal) :
    selfToDual r x = r * (x : ℕ → ZMod 2) := rfl

/-- Send a dual element `f` to the sequence `n ↦ f (coord n) n`. -/
def dualToSelfFun (f : Module.Dual (ℕ → ZMod 2) ideal) : ℕ → ZMod 2 :=
  fun n ↦ f (coord n) n

/-- `dualToSelfFun` is linear over `ℕ → ZMod 2`. -/
theorem dualToSelfFun_isLinear : IsLinearMap (ℕ → ZMod 2) dualToSelfFun := by
  constructor
  · intro f g
    rfl
  · intro r f
    rfl

/-- The linear map from the dual of the prefix-ones ideal to the product ring,
given by evaluation at each coordinate's prefix difference. -/
def dualToSelf :
    Module.Dual (ℕ → ZMod 2) ideal →ₗ[ℕ → ZMod 2] (ℕ → ZMod 2) :=
  IsLinearMap.mk' dualToSelfFun dualToSelfFun_isLinear

/-- `dualToSelf` evaluates a dual element on the standard prefix differences. -/
theorem dualToSelf_apply (f : Module.Dual (ℕ → ZMod 2) ideal) (n : ℕ) :
    dualToSelf f n = f (coord n) n := rfl

/-- `dualToSelf` is a left inverse of `selfToDual`. -/
theorem dualToSelf_comp_selfToDual :
    dualToSelf.comp selfToDual = LinearMap.id := by
  apply LinearMap.ext
  intro r
  funext n
  change selfToDual r (coord n) n = r n
  simp [selfToDual_apply, coord_apply_index]

/-- `selfToDual` is a left inverse of `dualToSelf`. -/
theorem selfToDual_comp_dualToSelf :
    selfToDual.comp dualToSelf = LinearMap.id := by
  ext f x n
  rw [LinearMap.comp_apply, selfToDual_apply]
  change dualToSelf f n * (x : ℕ → ZMod 2) n = f x n
  have hcomm : (coord n : ℕ → ZMod 2) • x = (x : ℕ → ZMod 2) • coord n := by
    apply Subtype.ext
    exact mul_comm _ _
  have hf : (coord n : ℕ → ZMod 2) • f x = (x : ℕ → ZMod 2) • f (coord n) := by
    rw [← f.map_smul, hcomm, f.map_smul]
  simpa [dualToSelf_apply, coord_apply_index, mul_comm] using congrFun hf.symm n

/-- The linear dual of the prefix-ones ideal is linearly isomorphic to the product ring
`ℕ → ZMod 2`, by coordinate evaluation with inverse given by restricted multiplication. -/
def dualEquiv :
    Module.Dual (ℕ → ZMod 2) ideal ≃ₗ[ℕ → ZMod 2] (ℕ → ZMod 2) :=
  LinearEquiv.ofLinear dualToSelf selfToDual
    dualToSelf_comp_selfToDual selfToDual_comp_dualToSelf

/-- `dualEquiv` is given on underlying maps by `dualToSelf`. -/
theorem dualEquiv_apply (f : Module.Dual (ℕ → ZMod 2) ideal) :
    dualEquiv f = dualToSelf f := rfl

/-- The inverse of `dualEquiv` is given on underlying maps by `selfToDual`. -/
theorem dualEquiv_symm_apply (r : ℕ → ZMod 2) :
    dualEquiv.symm r = selfToDual r := rfl

/-- The dual of the prefix-ones ideal is finitely generated. -/
instance instFinite_dual :
    Module.Finite (ℕ → ZMod 2) (Module.Dual (ℕ → ZMod 2) ideal) :=
  Module.Finite.equiv dualEquiv.symm

/-- The dual of the prefix-ones ideal is free, hence finite free with `instFinite_dual`. -/
instance instFree_dual :
    Module.Free (ℕ → ZMod 2) (Module.Dual (ℕ → ZMod 2) ideal) :=
  Module.Free.of_equiv dualEquiv.symm

end PrefixOnes
