/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.AutomorphismGroup

/-!
# Isomorphisms of automorphism-group algebraic spaces along a morphism

A morphism `f : X ⟶ Y` of algebraic stacks induces the Isom comparison
`Isom_X(p, p) ⟶ Isom_Y(p ≫ f, p ≫ f)` on the automorphism group algebraic
space of a field-valued point `p`. This map is an isomorphism of algebraic
spaces when it has the `isomorphisms` morphism property in the sense of
scheme-slice tests.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace automorphismGroup

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.IsIsoMap :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack Y], (X ⟶ Y) → FieldValuedPoint X → Prop)

#check (AlgebraicGeometry.AlgebraicStack.automorphismGroup.IsIsoMap_iff :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (p : FieldValuedPoint X),
    IsIsoMap f p ↔
      Groupoids.Hom.has (MorphismProperty.isomorphisms (AlgebraicSpace S))
        (isomComparison f p.toHom p.toHom))

end automorphismGroup

end AlgebraicGeometry.AlgebraicStack
