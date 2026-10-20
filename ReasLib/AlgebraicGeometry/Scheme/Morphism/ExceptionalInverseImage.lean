/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- An exceptional inverse image along `f` is a specified right adjoint `f !` to the
derived pushforward `R(f)_*`. -/
structure ExceptionalInverseImage {X Y : Scheme.{u}} (f : X ⟶ Y) where
  /-- The exceptional inverse-image functor associated to `f`. -/
  functor : RingedSpace.ModuleDerived Y.toRingedSpace ⥤
    RingedSpace.ModuleDerived X.toRingedSpace
  /-- The defining adjunction `R(f)_* ⊣ f !`. -/
  adjunction : RingedSpace.moduleDerivedPushforward f.toShHom ⊣ functor

namespace ExceptionalInverseImage

/-- Construct an exceptional inverse image from a specified right adjoint to `R(f)_*`. -/
def ofAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y)
    (functor : RingedSpace.ModuleDerived Y.toRingedSpace ⥤
      RingedSpace.ModuleDerived X.toRingedSpace)
    (adjunction : RingedSpace.moduleDerivedPushforward f.toShHom ⊣ functor) :
    ExceptionalInverseImage f :=
  ⟨functor, adjunction⟩

end ExceptionalInverseImage

end AlgebraicGeometry.Scheme
