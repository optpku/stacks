/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap82.Definition_82_13_1_PrincipalDivisor
import StacksCheckRecall

/-!
# Definition 82.13.1

The principal divisor of a rational unit on a good integral algebraic space,
as an `(n-1)`-cycle.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 82.13.1: In Situation 82.2.1, for good integral `X / B` with
`n = dim_δ(X)` and `φ ∈ (RationalFunction X)ˣ`, the principal divisor
associated to `φ` is the `(n-1)`-cycle
`div(φ) = div_X(φ) = Hom.principalDivisor f δ n hX φ`, equal to the Weil
divisor of Spaces over Fields, Definition 72.6.7, viewed as an `(n-1)`-cycle by
Lemma 82.12.1. -/
@[stacks 0EQ1]
#check
  (Hom.principalDivisor :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S}
      [UniversallyCatenary B] [IsQuasiSeparated B] (f : X ⟶ B)
      [QuasiSeparated f] [LocallyOfFiniteType f] [IsIntegral X]
      (δ : Points B → ℤ) [IsDimensionFunction δ] (n : ℤ),
      Hom.deltaDimension f δ (univIrreducibleClosed X) = n →
        (RationalFunction X)ˣ → Hom.cycleGroup f δ (n - 1))
