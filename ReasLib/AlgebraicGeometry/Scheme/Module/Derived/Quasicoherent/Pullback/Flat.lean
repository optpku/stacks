/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.ToUnbounded

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.Flat

/-- Flat pullback of module sheaves along a scheme morphism preserves
quasicoherence, supplying the landing condition for bounded-below pullback. -/
theorem pullbackPlusMapsTo {X Y : Scheme.{u}} (h : Y ⟶ X) [Flat h] :
    DerivedCategory.Plus.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ≤
      (DerivedCategory.Plus.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace)).inverseImage
          (ExactFunctor.Derived.Plus.functor
            (@RingedSpace.Hom.IsFlat.exactPullback _ _ h.toShHom
              (Scheme.Hom.isFlat_of_flat h))) := sorry

/-- Bounded-below derived pullback on complexes with quasicoherent cohomology
along a flat morphism of schemes. -/
noncomputable abbrev pullbackPlus {X Y : Scheme.{u}} (h : Y ⟶ X) [Flat h] :
    DerivedQCoh.Plus X ⥤ DerivedQCoh.Plus Y :=
  ObjectProperty.FullSubcategory.restrict
    (ExactFunctor.Derived.Plus.functor
      (@RingedSpace.Hom.IsFlat.exactPullback _ _ h.toShHom
        (Scheme.Hom.isFlat_of_flat h)))
    (pullbackPlusMapsTo h)

/-- After passage to the unbounded categories, bounded-below flat pullback is
naturally isomorphic to ordinary derived pullback. -/
theorem pullbackPlus_toUnbounded_isomorphic {X Y : Scheme.{u}}
    (h : Y ⟶ X) [Flat h] :
    IsIsomorphic
      (pullbackPlus h ⋙ DerivedCategory.Plus.CohomologyIn.toUnbounded
        (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace))
      (DerivedCategory.Plus.CohomologyIn.toUnbounded
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ⋙
        DerivedQCoh.pullback h) := sorry

/-- In a cartesian square, bounded-below pullback along the base-changed
horizontal morphism, with flatness inherited from the original one. -/
noncomputable abbrev pullbackPlusOfIsPullback
    {X' X Y' Y : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [Flat g] (sq : IsPullback g' f' f g) :
    DerivedQCoh.Plus X ⥤ DerivedQCoh.Plus X' :=
  @pullbackPlus X X' g'
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback sq.flip inferInstance)

end AlgebraicGeometry.Scheme.DerivedQCoh.Flat
