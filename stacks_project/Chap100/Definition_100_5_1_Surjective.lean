/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective

/-!
# Surjective morphisms of algebraic stacks

A morphism of algebraic stacks is surjective when the induced map of
associated point spaces is surjective. This extends the representable-by-algebraic-spaces
notion, without requiring representability of the morphism itself.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.Surjective :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.AlgebraicStack.surjective_iff_map_surjective :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y), Surjective f ↔ Function.Surjective (Points.map f))

#check (AlgebraicGeometry.AlgebraicStack.Surjective.map_surjective :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Surjective f], Function.Surjective (Points.map f))

#check (AlgebraicGeometry.AlgebraicStack.Surjective.of :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    {f : X ⟶ Y}, Function.Surjective (Points.map f) → Surjective f)

#check (AlgebraicGeometry.AlgebraicStack.Surjective.id :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X], Surjective (𝟙 X))

#check (AlgebraicGeometry.AlgebraicStack.Surjective.of_groupoidsHom :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Groupoids.Hom.Surjective f], Surjective f)

#check (AlgebraicGeometry.AlgebraicStack.Surjective.of_isIso :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [IsIso f], Surjective f)

end AlgebraicGeometry.AlgebraicStack
