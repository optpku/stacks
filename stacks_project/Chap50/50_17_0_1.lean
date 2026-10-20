module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Square
import StacksCheckRecall

open CategoryTheory

universe u

/- 50.17.0.1: the canonical blowup square with
`E = (I.comap b).subscheme`, `Z = I.subscheme`, and arrows
`j : E ⟶ X'`, `p : E ⟶ Z`, `b : X' ⟶ X`, and `i : Z ⟶ X`. -/
@[stacks 0FUS] #check (AlgebraicGeometry.IsBlowup.square :
  ∀ {X X' : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X)
    [AlgebraicGeometry.LocallyOfFinitePresentation I.subschemeι]
    [AlgebraicGeometry.IsBlowup b I],
    CategoryTheory.Square AlgebraicGeometry.Scheme.{u})

#check (AlgebraicGeometry.IsBlowup.square_isPullback :
  ∀ {X X' : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData) (b : X' ⟶ X)
    [AlgebraicGeometry.LocallyOfFinitePresentation I.subschemeι]
    [AlgebraicGeometry.IsBlowup b I],
    (AlgebraicGeometry.IsBlowup.square I b).IsPullback)
