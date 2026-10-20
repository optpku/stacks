/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen

/-!
# Universal openness from a relatively flat module of full support
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- A locally finitely presented morphism of algebraic spaces is universally open if its
source carries a finite-type quasi-coherent module of full support that is flat over the
target. -/
theorem universallyOpen_of_flatOver_of_moduleSupport_eq_univ
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] [LocallyOfFinitePresentation f]
    (hsupp : moduleSupport F = Set.univ) (hflat : flatOver F f) :
    UniversallyOpen f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
