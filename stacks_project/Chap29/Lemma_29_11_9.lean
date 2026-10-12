/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

@[expose] public section

open CategoryTheory

/- Lemma 29.11.9: the base change of an affine morphism is affine. -/
@[stacks 01SD] #check
  (AlgebraicGeometry.isAffineHom_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.IsAffineHom)
