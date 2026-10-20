/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat.Descent
import StacksCheckRecall

/-!
# Descent of flat morphisms of algebraic stacks along surjective flat base change

If the base change of a morphism of algebraic stacks along a surjective flat
morphism is flat, then the original morphism is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

open AlgebraicGeometry.AlgebraicStack

/- Lemma 101.25.4: Let `f : X ⟶ Y` be a morphism of algebraic stacks. Let
`g : Z ⟶ Y` be a surjective flat morphism of algebraic stacks. If the base
change `TwoFibreProduct.snd f g` is flat, then `f` is flat.

Stacks writes the base change as `Z ×_Y X ⟶ Z`; the Lean projection is
`TwoFibreProduct.snd f g`. -/
@[stacks 06PZ]
#check (AlgebraicGeometry.AlgebraicStack.Flat.of_twoFibreProduct_snd :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Surjective g] [Flat g]
    [Flat (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)],
    Flat f)

/- Flatness of a morphism of algebraic stacks follows from flatness of the
second projection of a bilimit `PseudoPullbackCone` against a surjective
flat morphism of algebraic stacks. -/
#check (AlgebraicGeometry.AlgebraicStack.Flat.of_isBilimit_snd :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [Surjective g] [Flat g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [Flat c.snd],
    Flat f)

/- After base change along a surjective flat morphism of algebraic stacks,
the original morphism is flat if and only if `TwoFibreProduct.snd f g` is
flat. -/
#check (AlgebraicGeometry.AlgebraicStack.Flat.twoFibreProduct_snd_iff :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [Surjective g] [Flat g],
    Flat (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) ↔ Flat f)
