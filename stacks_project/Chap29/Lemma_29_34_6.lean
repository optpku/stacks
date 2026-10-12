/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import StacksCheckRecall

/-!
# Lemma 29.34.6

An open immersion is smooth.

@stack 01VC
-/

@[expose] public section

universe u

/- Lemma 29.34.6

Any open immersion is smooth.
-/
@[stacks 01VC] #check
  (AlgebraicGeometry.instSmoothOfIsOpenImmersion :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.IsOpenImmersion f], AlgebraicGeometry.Smooth f)
