/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 29.11.8: the composition of affine morphisms is affine. -/
@[stacks 01SC] #check (@AlgebraicGeometry.instIsAffineHomCompScheme :
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsAffineHom f] [IsAffineHom g], IsAffineHom (f ≫ g))
