module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.Perfect
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 37.71.2: relative perfectness descends across a cartesian base change
whose base morphism is a finite-order thickening. -/
@[stacks 0DJY] #check
  (AlgebraicGeometry.IsFiniteOrderThickening.isPerfectOver_of_pullback :
    ∀ {X X' Y Y' : Scheme.{u}}
      (i : X ⟶ X') (f : X ⟶ Y) (f' : X' ⟶ Y') (j : Y ⟶ Y')
      (sq : IsPullback i f f' j)
      [Flat f'] [LocallyOfFinitePresentation f']
      [IsFiniteOrderThickening j]
      (E' : RingedSpace.ModuleDerived X'.toRingedSpace)
      (hE : RingedSpace.ModuleDerived.IsPerfectOver f.toShHom
        ((RingedSpace.modulePullbackDerived i.toShHom).obj E')),
      RingedSpace.ModuleDerived.IsPerfectOver f'.toShHom E')
