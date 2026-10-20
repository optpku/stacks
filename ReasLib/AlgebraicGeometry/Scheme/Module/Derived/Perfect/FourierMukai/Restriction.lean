/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.FourierMukai

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/-- The Fourier–Mukai transform associated to a perfect kernel, restricted to
perfect objects, when the source morphism is proper, flat, and of finite presentation. -/
noncomputable def perfect {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [Scheme.Hom.FinitePresentation f] [Flat f] [IsProper f]
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback f g).toRingedSpace) :
    @RingedSpace.ModuleDerived.Perfect X.toRingedSpace ⥤
      @RingedSpace.ModuleDerived.Perfect Y.toRingedSpace :=
  ObjectProperty.FullSubcategory.restrict (functor f g K.obj)
    (mapsPerfect_of_perfect_of_flat f g K.obj K.property)

/-- The restricted transform agrees with the ambient Fourier–Mukai transform after
inclusion of perfect objects. -/
noncomputable def perfect_comp_inclusionIso {S X Y : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S)
    [Scheme.Hom.FinitePresentation f] [Flat f] [IsProper f]
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback f g).toRingedSpace) :
    perfect f g K ⋙ RingedSpace.ModuleDerived.Perfect.ι ≅
      RingedSpace.ModuleDerived.Perfect.ι ⋙ functor f g K.obj :=
  ObjectProperty.FullSubcategory.restrict.compιIso (functor f g K.obj)
    (mapsPerfect_of_perfect_of_flat f g K.obj K.property)

end AlgebraicGeometry.Scheme.FourierMukai
