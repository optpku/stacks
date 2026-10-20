/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.KFlat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated

@[expose] public section

/-!
# Triangulated derived pullback on ringed spaces

The generic exactness API for total left derived functors equips derived module pullback
with its canonical shift comparison and triangulated structure.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.modulePullbackDerived

/-- Derived module pullback along a morphism of ringed spaces carries the canonical
comparison with integer shifts. -/
@[implicit_reducible]
noncomputable def commShift {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (modulePullbackDerived f).CommShift ℤ := by
  -- Local instance justification (defeq pin): opens-site K-flat definedness for this pullback.
  letI : Functor.LeftDerived.EverywhereDefined
      (modulePullbackToDerived f) (ModuleQis Y) :=
    RingedSite.Hom.modulePullbackToDerived.everywhereDefined (opensRingedSiteHom f)
  exact CategoryTheory.Functor.totalLeftDerived_commShift
    (modulePullbackToDerived f) (ModuleQis Y) DerivedCategory.Qh

/-- Derived module pullback along a morphism of ringed spaces is an exact functor of
triangulated categories. -/
theorem isTriangulated {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (modulePullbackDerived f).IsTriangulatedWith (commShift f) := by
  -- Local instance justification (defeq pin): opens-site K-flat definedness for this pullback.
  letI : Functor.LeftDerived.EverywhereDefined
      (modulePullbackToDerived f) (ModuleQis Y) :=
    RingedSite.Hom.modulePullbackToDerived.everywhereDefined (opensRingedSiteHom f)
  exact CategoryTheory.Functor.totalLeftDerived_isTriangulated
    (modulePullbackToDerived f) (ModuleQis Y) DerivedCategory.Qh

end AlgebraicGeometry.RingedSpace.modulePullbackDerived
