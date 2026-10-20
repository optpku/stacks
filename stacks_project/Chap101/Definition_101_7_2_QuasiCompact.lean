/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact

/-!
# Quasi-compact morphisms of algebraic stacks

Typed checks of the quasi-compact morphism property and its companion results.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

#check (AlgebraicGeometry.AlgebraicStack.QuasiCompact :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y], (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicStack.quasiCompact_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y),
    AlgebraicGeometry.AlgebraicStack.QuasiCompact f ↔
      ∀ {Z : GroupoidsOver S} {g : Z ⟶ Y} [AlgebraicStack Z]
        [AlgebraicGeometry.AlgebraicStack.IsQuasiCompact Z]
        (c : PseudoPullbackCone f g) [AlgebraicStack c.pt],
        c.IsBilimit → AlgebraicGeometry.AlgebraicStack.IsQuasiCompact c.pt)

#check (AlgebraicGeometry.AlgebraicStack.QuasiCompact.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    AlgebraicGeometry.AlgebraicStack.QuasiCompact (𝟙 X))

#check (AlgebraicGeometry.AlgebraicStack.QuasiCompact.of_isIso :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [IsIso f],
    AlgebraicGeometry.AlgebraicStack.QuasiCompact f)

#check (AlgebraicGeometry.AlgebraicStack.QuasiCompact.spec :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} [AlgebraicGeometry.AlgebraicStack.QuasiCompact f]
    {g : Z ⟶ Y} [AlgebraicGeometry.AlgebraicStack.IsQuasiCompact Z]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt],
    c.IsBilimit → AlgebraicGeometry.AlgebraicStack.IsQuasiCompact c.pt)

#check (AlgebraicGeometry.AlgebraicStack.QuasiCompact.isQuasiCompact :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicGeometry.AlgebraicStack.QuasiCompact f]
    [AlgebraicGeometry.AlgebraicStack.IsQuasiCompact Y],
    AlgebraicGeometry.AlgebraicStack.IsQuasiCompact X)

#check (AlgebraicGeometry.AlgebraicStack.instIsQuasiCompact_twoFibreProduct :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y)
    [AlgebraicGeometry.AlgebraicStack.QuasiCompact f]
    [AlgebraicGeometry.AlgebraicStack.IsQuasiCompact Z]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)],
    AlgebraicGeometry.AlgebraicStack.IsQuasiCompact
      (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g))
