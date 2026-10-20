/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleLocalAt.Near

/-!
# Neighbourhood étale-local properties of morphisms of algebraic spaces

The neighbourhood predicate is available through its shared mathematical owner.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.etaleLocalNear :
  ∀ {S : Scheme.{u}} (P : MorphismProperty Scheme.{u}) {X Y : AlgebraicSpace S},
    (X ⟶ Y) → AlgebraicGeometry.AlgebraicSpace.Points X → Prop)
