/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Cover
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Open
public import ReasLib.RingTheory.Module.Support.Flat

/-!
# Universal openness from a flat module of full support

This module gives a generalization-lifting criterion, and hence a universal-openness
criterion, for a scheme morphism carrying a relatively flat finite-type module of full support.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite-type quasicoherent module which is flat over a scheme morphism and has full support
forces the morphism to lift generalizations. -/
theorem generalizingMap_of_flatOver_of_moduleSupport_eq_univ
    {X Y : Scheme.{u}} (f : X ⟶ Y) (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
    (hsupp : moduleSupport ℱ = Set.univ) (hflat : flatOver ℱ f) :
    topologically GeneralizingMap f := sorry

/-- A locally finitely presented scheme morphism admitting a relatively flat finite-type
quasicoherent module of full support is universally open. -/
theorem universallyOpen_of_flatOver_of_moduleSupport_eq_univ
    {X Y : Scheme.{u}} (f : X ⟶ Y) (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] [LocallyOfFinitePresentation f]
    (hsupp : moduleSupport ℱ = Set.univ) (hflat : flatOver ℱ f) :
    UniversallyOpen f := sorry

end AlgebraicGeometry.Scheme.Modules
