/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Generation
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.ProjectionFormula
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Coproduct

/-!
# Projection formula for derived quasicoherent modules

This module records the projection formula for derived modules with quasicoherent cohomology
along quasi-compact and quasi-separated morphisms of schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- For a quasi-compact and quasi-separated morphism of schemes, the canonical
projection-formula mate is an isomorphism on derived modules with quasicoherent cohomology. -/
theorem isIso_projectionFormula {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends Y.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends Y.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization Y.toRingedSpace]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
    (K : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty Y.toRingedSpace)) :
    IsIso
      (RingedSpace.ModuleDerived.ProjectionFormula.leftMate f.toShHom E.obj K.obj) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
