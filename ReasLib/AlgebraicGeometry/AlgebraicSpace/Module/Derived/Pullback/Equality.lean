/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback

/-! # Equality transport for derived pullback of modules on algebraic spaces -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- Derived pullback along equal morphisms of algebraic spaces is isomorphic. -/
def pullbackCongr {S : Scheme.{u}} {Y X : AlgebraicSpace S} {f g : Y ⟶ X} (h : f = g) :
    pullback f ≅ pullback g :=
  eqToIso (congrArg pullback h)

/-- `pullbackCongr` is the functoriality of derived pullback on equal morphisms. -/
theorem pullbackCongr_eq {S : Scheme.{u}} {Y X : AlgebraicSpace S} {f g : Y ⟶ X}
    (h : f = g) : pullbackCongr h = eqToIso (congrArg pullback h) := rfl

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
