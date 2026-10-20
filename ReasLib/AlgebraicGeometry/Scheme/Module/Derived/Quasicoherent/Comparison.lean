/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.RingedSpace
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Comparison
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Equivalence

/-!
# Comparison for Derived Quasicoherent Modules

This module defines the canonical comparison from the derived category of quasicoherent
modules to ambient derived modules with quasicoherent cohomology. It also records the
restricted ambient derived pushforward and its compatibility with quasicoherent pushforward.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/-- Quasicoherent modules in the ringed-space presentation of a scheme form a weak Serre
subcategory. -/
instance ringedSpaceQuasiCoherent_isWeakSerreClass (X : Scheme.{u}) :
    ObjectProperty.IsWeakSerreClass
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) := sorry

end AlgebraicGeometry.Scheme.QCoh

namespace AlgebraicGeometry.Scheme.QCoh.Derived

/-- The ringed-space presentation of quasicoherent modules uses its standard derived
category. -/
noncomputable instance ringedSpaceHasDerivedCategory (X : Scheme.{u}) :
    HasDerivedCategory (RingedSpace.QCoh X.toRingedSpace) :=
  HasDerivedCategory.standard (RingedSpace.QCoh X.toRingedSpace)

end AlgebraicGeometry.Scheme.QCoh.Derived

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The canonical comparison from the derived category of quasicoherent modules to ambient
derived modules whose cohomology is quasicoherent. -/
noncomputable abbrev comparison (X : Scheme.{u}) :
    DerivedCategory (QCoh X) ⥤
      DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) :=
  (QCoh.ringedSpaceEquivalence X).mapDerivedCategory.functor ⋙
    DerivedCategory.CohomologyIn.Comparison.functor
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)

namespace comparison

/-- Forgetting the canonical comparison recovers the derived quasicoherent inclusion after
changing from the scheme presentation to the ringed-space presentation. -/
theorem compInclusion_isomorphic (X : Scheme.{u}) :
    IsIsomorphic
      (comparison X ⋙
        (DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι)
      ((QCoh.ringedSpaceEquivalence X).mapDerivedCategory.functor ⋙
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace).ι.mapDerivedCategory) := sorry

end comparison

namespace pushforwardCohomologyIn

/-- Derived pushforward along a quasi-compact, quasi-separated morphism preserves ambient
derived modules with quasicoherent cohomology. -/
theorem mapsTo {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ≤
      (DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace)).inverseImage
          (RingedSpace.moduleDerivedPushforward f.toShHom) := sorry

end pushforwardCohomologyIn

/-- Ambient derived pushforward restricted to complexes with quasicoherent cohomology. -/
noncomputable def pushforwardCohomologyIn {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace) ⥤
      DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace) :=
  (DerivedCategory.cohomologyIn
    (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace)).lift
      ((DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
          RingedSpace.moduleDerivedPushforward f.toShHom)
      (fun E ↦ pushforwardCohomologyIn.mapsTo f E.obj E.property)

namespace pushforwardCohomologyIn

/-- Forgetting the restricted ambient pushforward recovers ambient derived pushforward. -/
noncomputable def inclusionIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    pushforwardCohomologyIn f ⋙
        (DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace)).ι ≅
      (DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
          RingedSpace.moduleDerivedPushforward f.toShHom :=
  (DerivedCategory.cohomologyIn
    (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace)).liftCompιIso
      ((DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
          RingedSpace.moduleDerivedPushforward f.toShHom)
      (fun E ↦ mapsTo f E.obj E.property)

end pushforwardCohomologyIn

/-- For a morphism of Noetherian schemes, canonical derived quasicoherent pushforward and
restricted ambient derived pushforward agree after applying the comparison functors. -/
theorem pushforwardComparison_isomorphic {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y] :
    IsIsomorphic
      (QCoh.Derived.pushforward f ⋙ comparison Y)
      (comparison X ⋙ pushforwardCohomologyIn f) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
