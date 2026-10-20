/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.BaseChange
import StacksCheckRecall

/-!
# Base change of transferred morphism properties of algebraic spaces

If a morphism property of algebraic spaces is stable under base change, then
so is its transfer to morphisms of presheaves representable by algebraic
spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

/- Lemma 80.4.2: let `S` be a scheme. Let `P` be a property as in
Definition 80.4.1. For a fibre square of presheaves on `(Sch/S)_fppf`, if
`a : F ⟶ G` is representable by algebraic spaces and has `P`, then so does
its base change `a' : G' ×_G F ⟶ G'`. -/
@[stacks 046F] #check
  (AlgebraicGeometry.AlgebraicSpace.relativeAlgebraicSpaces.isStableUnderBaseChange :
    ∀ {S : Scheme.{u}} {P : MorphismProperty (AlgebraicSpace S)}
      [P.IsStableUnderBaseChange],
      (AlgebraicGeometry.AlgebraicSpace.relativeAlgebraicSpaces P).IsStableUnderBaseChange)
