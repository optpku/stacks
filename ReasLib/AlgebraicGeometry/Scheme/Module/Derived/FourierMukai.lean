/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tensor
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/-- The Fourier--Mukai transform formed by derived pullback, fixed-right derived tensoring with
the kernel, and derived pushforward along the second projection. -/
noncomputable def functor {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace) :
    RingedSpace.ModuleDerived X.toRingedSpace ⥤ RingedSpace.ModuleDerived Y.toRingedSpace :=
  RingedSpace.modulePullbackDerived (Limits.pullback.fst f g).toLRSHom.toShHom ⋙
    DerivedCategory.DerivedTensor.Right.functor K ⋙
      RingedSpace.moduleDerivedPushforward (Limits.pullback.snd f g).toShHom

/-- The Fourier--Mukai transform admits a triangulated structure. -/
theorem hasTriangulatedStructure {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace) :
    (functor f g K).HasTriangulatedStructure := sorry

/-- The Fourier--Mukai transform restricted to full subcategories selected by object properties
that it preserves. -/
noncomputable def restrict {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)
    {P : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)}
    {Q : ObjectProperty (RingedSpace.ModuleDerived Y.toRingedSpace)}
    (h : P ≤ Q.inverseImage (functor f g K)) : P.FullSubcategory ⥤ Q.FullSubcategory :=
  ObjectProperty.FullSubcategory.restrict (functor f g K) h

/-- The inclusion comparison for a restricted Fourier--Mukai transform. -/
noncomputable def restrict_inclusionIso {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)
    {P : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)}
    {Q : ObjectProperty (RingedSpace.ModuleDerived Y.toRingedSpace)}
    (h : P ≤ Q.inverseImage (functor f g K)) :
    restrict f g K h ⋙ Q.ι ≅ P.ι ⋙ functor f g K :=
  ObjectProperty.FullSubcategory.restrict.compιIso (functor f g K) h

/-- A restricted Fourier--Mukai transform between triangulated full subcategories admits a
triangulated structure. -/
theorem restrict_hasTriangulatedStructure {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)
    {P : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)}
    {Q : ObjectProperty (RingedSpace.ModuleDerived Y.toRingedSpace)}
    (h : P ≤ Q.inverseImage (functor f g K)) [P.IsTriangulated] [Q.IsTriangulated] :
    (restrict f g K h).HasTriangulatedStructure := sorry

end AlgebraicGeometry.Scheme.FourierMukai
