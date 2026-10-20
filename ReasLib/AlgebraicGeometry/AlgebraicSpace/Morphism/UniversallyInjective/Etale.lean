/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective

/-!
# Universal injectivity from étale base changes

A locally finite type morphism of algebraic spaces is universally injective if
every étale base change induces an injective map on underlying point spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.UniversallyInjective

/-- A locally finite type morphism of algebraic spaces over a scheme is
universally injective if every étale base change induces an injective map on
underlying point spaces. -/
theorem of_locallyOfFiniteType_etale_pointsInjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f]
    (h_etale : ∀ {V : AlgebraicSpace S} (g : V ⟶ Y),
      Etale g → Function.Injective (Points.map (pullback.snd f g))) :
    UniversallyInjective f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.UniversallyInjective
