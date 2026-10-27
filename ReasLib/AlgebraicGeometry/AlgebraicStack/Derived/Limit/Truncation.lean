/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.QuasiCoherent
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Lower.Tower.Cone
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Comparison.Definition

/-!
# Derived limits of canonical truncations on algebraic stacks
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicStack GroupoidsOver

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A derived fppf module on an algebraic stack whose cohomology sheaves are locally
quasi-coherent and satisfy flat base change admits a distinguished homotopy-limit
presentation compatible with its canonical lower-truncation projections. -/
theorem lowerTruncationComparison_id
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (K : ModuleDerived X)
    (hK : DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X) K) :
    Nonempty (HomotopyLimit.Comparison (DerivedCategory.Truncation.Lower.cone K)
      (𝟙 K)) := sorry

/-- A morphism from a derived fppf module on an algebraic stack to a homotopy limit
of its canonical lower truncations is an isomorphism if it respects the canonical
projections and the cohomology sheaves are locally quasi-coherent and satisfy flat
base change. -/
theorem lowerTruncationComparison_isIso
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (K : ModuleDerived X)
    (hK : DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X) K)
    {L : ModuleDerived X} (c : K ⟶ L)
    (hc : Nonempty (HomotopyLimit.Comparison
      (DerivedCategory.Truncation.Lower.cone K) c)) :
    IsIso c := sorry

end AlgebraicGeometry.AlgebraicStack
