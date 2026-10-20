/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Dimension
import StacksCheckRecall

/-!
# Effective Cartier divisors drop local dimension

An effective Cartier divisor on an algebraic space has strictly smaller local
dimension at every point of finite local dimension on the ambient space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 71.6.5: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `i : D ⟶ X` be an effective Cartier divisor. Let `x` be a point of `|D|`.
If `dimensionAt (Points.map i x) < ⊤`, then
`dimensionAt x < dimensionAt (Points.map i x)`. -/
@[stacks 083T] #check
  (AlgebraicGeometry.AlgebraicSpace.IsEffectiveCartierDivisor.dimensionAt_lt :
    ∀ {S : Scheme.{u}} {D X : AlgebraicSpace S} (i : D ⟶ X)
      [IsEffectiveCartierDivisor i] (x : Points D),
      dimensionAt (Points.map i x) < ⊤ →
        dimensionAt x < dimensionAt (Points.map i x))
