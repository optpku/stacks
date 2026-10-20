/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen

/-!
# Flat morphisms locally of finite presentation are universally open

A flat morphism of algebraic spaces that is locally of finite presentation is
universally open.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A flat morphism of algebraic spaces that is locally of finite presentation
is universally open. -/
instance (priority := low) UniversallyOpen.of_flat {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] :
    UniversallyOpen f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
