/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap110.Lemma_110_34_2

@[expose] public section

namespace PrefixOnes

/-- Remark 110.34.3 (1): the prefix-ones ideal `I` is a non-finitely generated
projective module over `R = ℕ → ZMod 2`. Projectivity is `instProjective`. -/
@[stacks 0H8D]
theorem not_finite : ¬ Module.Finite (ℕ → ZMod 2) ideal := sorry

/-- Consecutive prefix-ones differences `seq (n + 1) - seq n` lie in the prefix-ones ideal. -/
theorem coord_mem (n : ℕ) : seq (n + 1) - seq n ∈ ideal := sorry

/-- The standard prefix difference `seq (n + 1) - seq n` in the prefix-ones ideal, supported at `n`. -/
def coord (n : ℕ) : ideal :=
  ⟨seq (n + 1) - seq n, coord_mem n⟩

/-- The underlying sequence of `coord n` is the consecutive prefix-ones difference. -/
theorem coord_apply (n : ℕ) : (coord n : ℕ → ZMod 2) = seq (n + 1) - seq n := sorry

/-- Left multiplication by an element of `ℕ → ZMod 2`, restricted along the inclusion of
the prefix-ones ideal, as a map into the dual module. -/
def selfToDual :
    (ℕ → ZMod 2) →ₗ[ℕ → ZMod 2] Module.Dual (ℕ → ZMod 2) ideal :=
  LinearMap.lcomp (ℕ → ZMod 2) (ℕ → ZMod 2) (Submodule.subtype ideal) ∘ₗ
    LinearMap.mul (ℕ → ZMod 2) (ℕ → ZMod 2)

/-- `selfToDual r` acts on the prefix-ones ideal by multiplication by `r`. -/
theorem selfToDual_apply (r : ℕ → ZMod 2) (x : ideal) :
    selfToDual r x = r * (x : ℕ → ZMod 2) := sorry

/-- Send a dual element `f` to the sequence `n ↦ f (coord n) n`. -/
def dualToSelfFun (f : Module.Dual (ℕ → ZMod 2) ideal) : ℕ → ZMod 2 :=
  fun n ↦ f (coord n) n

/-- `dualToSelfFun` is linear over `ℕ → ZMod 2`. -/
theorem dualToSelfFun_isLinear : IsLinearMap (ℕ → ZMod 2) dualToSelfFun := sorry

/-- The inverse map `Module.Dual (ℕ → ZMod 2) ideal →ₗ[ℕ → ZMod 2] (ℕ → ZMod 2)`. -/
def dualToSelf :
    Module.Dual (ℕ → ZMod 2) ideal →ₗ[ℕ → ZMod 2] (ℕ → ZMod 2) :=
  IsLinearMap.mk' dualToSelfFun dualToSelfFun_isLinear

/-- `dualToSelf` evaluates a dual element on the standard prefix differences. -/
theorem dualToSelf_apply (f : Module.Dual (ℕ → ZMod 2) ideal) (n : ℕ) :
    dualToSelf f n = f (coord n) n := sorry

/-- `dualToSelf` is a left inverse of `selfToDual`. -/
theorem dualToSelf_comp_selfToDual :
    dualToSelf.comp selfToDual = LinearMap.id := sorry

/-- `selfToDual` is a left inverse of `dualToSelf`. -/
theorem selfToDual_comp_dualToSelf :
    selfToDual.comp dualToSelf = LinearMap.id := sorry

/-- Remark 110.34.3 (2): `Module.Dual (ℕ → ZMod 2) ideal ≃ₗ[ℕ → ZMod 2] (ℕ → ZMod 2)`,
i.e. Hom over `ℕ → ZMod 2` from the prefix-ones ideal into the ring is linearly isomorphic
to the ring. -/
@[stacks 0H8D]
def dualEquiv :
    Module.Dual (ℕ → ZMod 2) ideal ≃ₗ[ℕ → ZMod 2] (ℕ → ZMod 2) :=
  LinearEquiv.ofLinear dualToSelf selfToDual
    dualToSelf_comp_selfToDual selfToDual_comp_dualToSelf

/-- `dualEquiv` is given on underlying maps by `dualToSelf`. -/
theorem dualEquiv_apply (f : Module.Dual (ℕ → ZMod 2) ideal) :
    dualEquiv f = dualToSelf f := sorry

/-- The inverse of `dualEquiv` is given on underlying maps by `selfToDual`. -/
theorem dualEquiv_symm_apply (r : ℕ → ZMod 2) :
    dualEquiv.symm r = selfToDual r := sorry

/-- The dual of the prefix-ones ideal is finitely generated. -/
instance instFinite_dual :
    Module.Finite (ℕ → ZMod 2) (Module.Dual (ℕ → ZMod 2) ideal) := sorry

/-- The dual of the prefix-ones ideal is free, hence finite free with `instFinite_dual`. -/
instance instFree_dual :
    Module.Free (ℕ → ZMod 2) (Module.Dual (ℕ → ZMod 2) ideal) := sorry

end PrefixOnes
