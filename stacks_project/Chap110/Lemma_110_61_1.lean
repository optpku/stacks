/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.Limit.Truncation
import StacksCheckRecall

/-!
# Derived limits of canonical truncations on algebraic stacks
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicStack GroupoidsOver

universe u

/- Lemma 110.61.1: a derived fppf module with locally quasi-coherent cohomology
satisfying flat base change is the derived limit of its canonical lower truncations,
with a distinguished Milnor triangle compatible with the canonical projections. -/
@[stacks 08IY] #check (AlgebraicGeometry.AlgebraicStack.lowerTruncationComparison_id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (K : ModuleDerived X)
    (hK : DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X) K),
    Nonempty (HomotopyLimit.Comparison (DerivedCategory.Truncation.Lower.cone K)
      (𝟙 K)))

#check (AlgebraicGeometry.AlgebraicStack.lowerTruncationComparison_isIso :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (K : ModuleDerived X)
    (hK : DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X) K)
    {L : ModuleDerived X} (c : K ⟶ L)
    (hc : Nonempty (HomotopyLimit.Comparison
      (DerivedCategory.Truncation.Lower.cone K) c)),
    IsIso c)
