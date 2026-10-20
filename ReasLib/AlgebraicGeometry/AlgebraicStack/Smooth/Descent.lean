/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# Descent of smoothness for morphisms of algebraic stacks

Smoothness descends along surjective, flat, locally finitely presented morphisms
of algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Smooth

/-- A morphism of algebraic stacks is smooth if its base change along a
surjective, flat, locally finitely presented morphism is smooth. -/
@[stacks 0DN7]
theorem of_twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    [Smooth (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)] :
    Smooth f := sorry

/-- Smoothness of a morphism of algebraic stacks follows from smoothness of the
second projection of a bilimit `PseudoPullbackCone` against a surjective, flat,
locally finitely presented morphism of algebraic stacks. -/
theorem of_isBilimit_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y}
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [Smooth c.snd] :
    Smooth f := sorry

/-- After base change along a surjective, flat, locally finitely presented
morphism of algebraic stacks, the second projection is smooth if and only if
the original morphism is smooth. -/
theorem twoFibreProduct_snd_iff {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g] :
    Smooth (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) ↔ Smooth f := sorry

end AlgebraicGeometry.AlgebraicStack.Smooth
