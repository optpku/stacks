/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.PseudoCoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

@[expose] public section

open CategoryTheory

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.IsFiniteOrderThickening

/-- Relative perfectness descends across a cartesian base change whose base morphism is a
finite-order thickening. -/
theorem isPerfectOver_of_pullback
    {X X' Y Y' : Scheme.{u}}
    (i : X ⟶ X') (f : X ⟶ Y) (f' : X' ⟶ Y') (j : Y ⟶ Y')
    (sq : IsPullback i f f' j)
    [Flat f'] [LocallyOfFinitePresentation f']
    [IsFiniteOrderThickening j]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f'.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f'.toShHom).restrict U.isOpenEmbedding))]
    (E' : RingedSpace.ModuleDerived X'.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfectOver f.toShHom
      ((RingedSpace.modulePullbackDerived i.toShHom).obj E')) :
    RingedSpace.ModuleDerived.IsPerfectOver f'.toShHom E' := sorry

end AlgebraicGeometry.IsFiniteOrderThickening
