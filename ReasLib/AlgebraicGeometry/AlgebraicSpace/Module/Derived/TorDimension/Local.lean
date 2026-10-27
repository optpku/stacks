/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.TorDimension.Relative.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.ChartRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Square
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Local
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RelativeRestriction

/-! # Locally finite relative Tor dimension on algebraic spaces -/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory
open RingedSpace.ModuleDerived (LocallyHasFiniteTorDimension relativeRestriction)

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- For a complex with quasi-coherent cohomology, locally finite Tor dimension over
inverse-image coefficients is equivalent to locally finite Tor dimension on every
étale scheme square. -/
theorem hasLocallyFiniteTorDimensionOver_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [∀ sq : EtaleSquare f,
      (Functor.Homotopy.toDerived
        (SmallEtaleModuleGlueing.restrictFunctor_hom sq.left ⋙ Modules.restrictToScheme sq.left.left ⋙
          Scheme.Modules.toRingedSpace sq.left.left.left)).HasLeftDerivedFunctor (ModuleQis X)]
    [∀ sq : EtaleSquare f,
      ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding))]
    (E : ModuleDerived X) (hE : derivedQuasiCoherentModuleProperty X E) :
    locallyFiniteTorDimensionOver f E ↔
      ∀ sq : EtaleSquare f,
        LocallyHasFiniteTorDimension
          (X := RingedSpace.Hom.inverseImageBase sq.map.left.toShHom)
          ((relativeRestriction (sq.map.left).toShHom).obj
            ((restrictToEtaleChart sq.left).obj E)) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
