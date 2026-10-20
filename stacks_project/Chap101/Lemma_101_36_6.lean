/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Unramified.Characterization

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 101.36.6: For a morphism of algebraic stacks, unramifiedness is
equivalent to the DM condition and unramifiedness of all étale algebraic-space
comparisons on arbitrary algebraic-space pullbacks, and to the existence of a
surjective, flat, locally finitely presented algebraic-space cover of the target
with a surjective étale algebraic-space comparison whose composite is unramified. -/
@[stacks 0CIY] #check (AlgebraicGeometry.AlgebraicStack.Unramified.tfae :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y),
    List.TFAE
      [AlgebraicStack.Unramified f,
        AlgebraicStack.DM f ∧ AlgebraicStack.Unramified.forallEtaleOnPullbacks f,
        AlgebraicStack.Unramified.existsFppfEtaleSquare f])
