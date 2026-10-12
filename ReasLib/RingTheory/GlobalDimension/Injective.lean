/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Abelian.HomologicalDimension.Uniform
public import ReasLib.RingTheory.GlobalDimension.Basic

@[expose] public section

/-!
# Injective Consequences of Global Dimension

A ring-level global-dimension bound is defined projectively, but it controls the injective
dimension of every module and every higher extension group as well.
-/

open CategoryTheory

universe u v

namespace HasGlobalDimensionLE

variable {R : Type u} [Ring R] {n : ℕ}

/-- A global-dimension bound gives every module the same injective-dimension bound. -/
@[stacks 00O6 "uniform injective-dimension bound"]
theorem hasInjectiveDimensionLE [HasGlobalDimensionLE R n]
    (M : ModuleCat.{v} R) : HasInjectiveDimensionLE M n := sorry

/-- The numerical injective dimension of a module is bounded by the global dimension bound. -/
@[stacks 00O6 "numerical injective-dimension bound"]
theorem injectiveDimension_le [HasGlobalDimensionLE R n]
    (M : ModuleCat.{v} R) : injectiveDimension M ≤ n := sorry

/-- All extension groups above a global-dimension bound are subsingletons. -/
@[stacks 00O6 "higher Ext vanishing"]
theorem ext_subsingleton [Small.{v} R] [HasGlobalDimensionLE R n]
    (X Y : ModuleCat.{v} R) (i : ℕ) (hi : n < i) :
    Subsingleton (Abelian.Ext X Y i) := sorry

end HasGlobalDimensionLE

/-- The injective-dimension consequence of a ring-level global bound is canonical and available
to typeclass search. -/
instance instHasInjectiveDimensionLE
    {R : Type u} [Ring R] (n : ℕ) [HasGlobalDimensionLE R n]
    (M : ModuleCat.{v} R) : HasInjectiveDimensionLE M n := sorry
