/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.DerivedCategory.Truncation.Lower.Comparison
public import stacks_project.Chap104.Definition_104_5_1_DerivedQCoh

/-!
# Derived limits of canonical truncations on algebraic stacks
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicStack GroupoidsOver
open DerivedCategory.Truncation.Lower

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 110.61.1: if `X` is an algebraic stack and `K` is an object of
`D(𝒪_X)` whose cohomology sheaves are locally quasi-coherent
(Definition 96.12.1) and have the flat base change property
(Definition 103.7.1), then there is a distinguished triangle
`K ⟶ ∏_{n ≥ 0} τ≥(-n) K ⟶ ∏_{n ≥ 0} τ≥(-n) K ⟶ K⟦1⟧` in `D(𝒪_X)`.
In other words, `K` is the derived limit of its canonical truncations. -/
@[stacks 08IY]
theorem isHomotopyLimit_lowerTruncationTower
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (K : ModuleDerived X)
    (hK : DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X) K) :
    HomotopyLimit.IsOf (tower K) K := sorry

/-- A morphism from `K` to a derived limit of its canonical lower
truncations is an isomorphism when the cohomology sheaves of `K` are
locally quasi-coherent and have the flat base change property. -/
theorem lowerTruncationComparison_isIso
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (K : ModuleDerived X)
    (hK : DerivedCategory.cohomologyIn (FppfModules.lqcohFbc X) K)
    {L : ModuleDerived X} (c : K ⟶ L)
    (hc : Comparison.Exists K c) :
    IsIso c := sorry

end AlgebraicGeometry.AlgebraicStack
