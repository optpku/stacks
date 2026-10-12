/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative
import StacksCheckRecall

/-!
# Definition 31.18.2

Relative effective Cartier divisors.

@stack 062T
-/

@[expose] public section

open CategoryTheory

universe u

/- Definition 31.18.2: A relative effective Cartier divisor on `X/S` is an effective Cartier
divisor `D` on `X` whose induced morphism to `S` is flat. -/
@[stacks 062T] #check
  (AlgebraicGeometry.IsRelativeEffectiveCartierDivisor :
    {X S : AlgebraicGeometry.Scheme.{u}} → (X ⟶ S) → X.IdealSheafData → Prop)

#check
  (AlgebraicGeometry.isRelativeEffectiveCartierDivisor_iff :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (D : X.IdealSheafData),
      AlgebraicGeometry.IsRelativeEffectiveCartierDivisor f D ↔
        AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι ∧
          AlgebraicGeometry.Flat (D.subschemeι ≫ f))
