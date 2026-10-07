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
