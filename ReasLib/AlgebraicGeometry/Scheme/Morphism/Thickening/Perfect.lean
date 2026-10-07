module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.PseudoCoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsFiniteOrderThickening

/-- Relative perfectness descends across a cartesian base change whose base morphism is a
finite-order thickening. -/
theorem isPerfectOver_of_pullback
    {X X' Y Y' : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) (f' : X' ⟶ Y') (j : Y ⟶ Y')
    (sq : IsPullback i f f' j)
    [Flat f'] [LocallyOfFinitePresentation f']
    [IsFiniteOrderThickening j]
    (E' : RingedSpace.ModuleDerived X'.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfectOver f.toShHom
      ((RingedSpace.modulePullbackDerived i.toShHom).obj E')) :
    RingedSpace.ModuleDerived.IsPerfectOver f'.toShHom E' := sorry

end AlgebraicGeometry.IsFiniteOrderThickening
