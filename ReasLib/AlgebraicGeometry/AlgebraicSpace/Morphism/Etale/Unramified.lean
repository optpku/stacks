/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified

/-!
# Étale and unramified morphisms of algebraic spaces

Étale morphisms are unramified. Locally finitely presented, flat, unramified
morphisms are étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An étale morphism of algebraic spaces is unramified. -/
instance unramified_of_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] : Unramified f :=
  sorry

/-- A locally finitely presented, flat, unramified morphism of algebraic spaces
is étale. -/
instance etale_of_locallyOfFinitePresentation_of_flat_of_unramified
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [Flat f] [Unramified f] : Etale f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
