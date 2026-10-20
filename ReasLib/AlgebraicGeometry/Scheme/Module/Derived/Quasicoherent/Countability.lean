/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Duality
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections.MayerVietoris
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Derived
public import ReasLib.AlgebraicGeometry.Scheme.CompactOpenInduction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Tensor.Affine
public import ReasLib.CategoryTheory.DerivedCategory.Ext

/-!
# Countability for derived quasicoherent modules

This module records countability of hypercohomology and restricted extension groups after
tensoring a derived quasicoherent module with a perfect derived module.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.DerivedCategory
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- If all cohomology sheaves of a derived quasicoherent module have countable sections on
affine opens, then its derived tensor product with a perfect module has countable
hypercohomology on every quasi-compact open. -/
theorem tensorOpenHypercohomologyCountable {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (K : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent X)
    (hK : ∀ j : ℤ, ∀ V : X.affineOpens,
      Countable (RingedSpace.moduleSectionsOnOpen
        (RingedSpace.ModuleDerived.cohomologySheaf K.obj j) (V : X.Opens)))
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E) (U : X.Opens)
    (hU : IsCompact (U : Set X)) (i : ℤ) :
    Countable (RingedSpace.moduleOpenHypercohomology X.toRingedSpace U
      ((DerivedTensor.Right.functor E).obj K.obj) i) := sorry

/-- If all cohomology sheaves of a derived quasicoherent module have countable sections on
affine opens, then every extension group from a perfect module to it, after restriction to a
quasi-compact open, is countable. -/
theorem restrictedExtCountable {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (K : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent X)
    (hK : ∀ j : ℤ, ∀ V : X.affineOpens,
      Countable (RingedSpace.moduleSectionsOnOpen
        (RingedSpace.ModuleDerived.cohomologySheaf K.obj j) (V : X.Opens)))
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E) (U : X.Opens)
    (hU : IsCompact (U : Set X)) (i : ℤ) :
    Countable
      (Ext⁽i⁾((RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace U).obj E,
        (RingedSpace.moduleRestrictionToOpenDerived X.toRingedSpace U).obj K.obj)) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
