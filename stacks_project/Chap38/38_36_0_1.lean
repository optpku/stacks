module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Square
import StacksCheckRecall

open CategoryTheory

universe u

/- 38.36.0.1: the canonical blowup square with center `I.subscheme` and exceptional
subscheme `(I.comap b).subscheme`. -/
@[stacks 0EV5] #check (AlgebraicGeometry.IsBlowup.square :
  ∀ {X X' : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X)
    [AlgebraicGeometry.LocallyOfFinitePresentation I.subschemeι]
    [AlgebraicGeometry.IsBlowup b I],
    CategoryTheory.Square AlgebraicGeometry.Scheme.{u})

#check (AlgebraicGeometry.IsBlowup.square_isPullback :
  ∀ {X X' : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X)
    [AlgebraicGeometry.LocallyOfFinitePresentation I.subschemeι]
    [AlgebraicGeometry.IsBlowup b I],
    (AlgebraicGeometry.IsBlowup.square I b).IsPullback)
