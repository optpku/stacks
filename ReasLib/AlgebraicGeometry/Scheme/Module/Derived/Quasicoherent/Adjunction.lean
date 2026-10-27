/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pullback
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction

/-!
# Derived pullback-pushforward adjunction for quasicoherent cohomology

The ambient derived pullback-pushforward adjunction on module sheaves restricts to the full
subcategories of derived modules with quasicoherent cohomology.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Legacy absolute-derived pair condition. This theorem is retained for existing callers;
the actual QCoh adjunction below does not use it to construct maps. -/
theorem pullbackPushforwardAdjunctionHasPair
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom) := sorry

/-- Derived pullback is left adjoint to derived pushforward after restricting both functors
to derived modules with quasicoherent cohomology. -/
noncomputable def pullbackPushforwardAdjunction
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    pullback f ⊣ pushforwardCohomologyIn f :=
  ObjectProperty.FullSubcategory.adjunction
    (RingedSpace.modulePullbackDerived f.toShHom)
    (RingedSpace.moduleDerivedPushforward f.toShHom)
    (RingedSpace.moduleDerivedAdjunction f.toShHom)
    (pullback.mapsTo f) (pushforwardCohomologyIn.mapsTo f)

end AlgebraicGeometry.Scheme.DerivedQCoh
