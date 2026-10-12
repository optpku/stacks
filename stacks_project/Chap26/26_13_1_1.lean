/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Stalk

@[expose] public section

open AlgebraicGeometry

universe u

variable (X : Scheme.{u}) (x : X)

/- Equation 26.13.1.1: the canonical morphism from the spectrum of the
stalk `𝒪_{X,x}` to `X`. -/
@[stacks 02NA] #check X.fromSpecStalk x
