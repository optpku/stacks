/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiFinite

/-!
# Quasi-finite morphisms of algebraic stacks

Typed checks of the quasi-finite morphism property and its companion results.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.QuasiFinite :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y], (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicStack.quasiFinite_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    QuasiFinite f ↔ LocallyQuasiFinite f ∧ QuasiCompact f)

#check (AlgebraicGeometry.AlgebraicStack.QuasiFinite.spec :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [QuasiFinite f],
    LocallyQuasiFinite f ∧ QuasiCompact f)

#check (AlgebraicGeometry.AlgebraicStack.QuasiFinite.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    QuasiFinite (𝟙 X))

#check (AlgebraicGeometry.AlgebraicStack.QuasiFinite.of_isIso :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsIso f],
    QuasiFinite f)

#check (AlgebraicGeometry.AlgebraicStack.QuasiFinite.instOfLocallyQuasiFiniteQuasiCompact :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [LocallyQuasiFinite f] [QuasiCompact f], QuasiFinite f)

#check (AlgebraicGeometry.AlgebraicStack.QuasiFinite.of_toGroupoids :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.QuasiFinite f],
    QuasiFinite (AlgebraicSpace.toGroupoids.map f))

end AlgebraicGeometry.AlgebraicStack
