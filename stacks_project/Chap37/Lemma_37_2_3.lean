module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 37.2.3: any thickening of an affine scheme is affine. -/
@[stacks 06AD]
#check (AlgebraicGeometry.IsThickening.isAffine :
  ∀ {X X' : Scheme.{u}} (i : X ⟶ X') [IsThickening i] [IsAffine X], IsAffine X')
