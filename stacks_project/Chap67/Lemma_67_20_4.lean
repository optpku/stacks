/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
import StacksCheckRecall

/-!
# Composition of affine morphisms of algebraic spaces

The composition of a pair of affine morphisms of algebraic spaces is affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

/- Lemma 67.20.4: The composition of affine morphisms of algebraic spaces is affine. -/
@[stacks 03WH] #check
  (AlgebraicGeometry.AlgebraicSpace.Affine.isStableUnderComposition :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.AlgebraicSpace.Affine S : MorphismProperty (AlgebraicSpace S)))
