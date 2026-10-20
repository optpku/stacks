/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Isom.LocallyOfFiniteType
import StacksCheckRecall

/-!
# Lemma 101.3.1

For an algebraic stack `X` and fibre objects `x, y` over a scheme `T`, the
structure morphism `Isom_X(x, y) ⟶ T` is locally of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids

universe u

/- Lemma 101.3.1: Let `X` be an algebraic stack. Let `T` be a scheme and let
`x`, `y` be objects of the fibre category of `X` over `T`. Then the morphism
`Isom_X(x, y) ⟶ T` is locally of finite type. -/
@[stacks 04XR] #check (AlgebraicGeometry.AlgebraicStack.Isom.locallyOfFiniteType_isomOverHom :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (x y : X.p.Fiber T),
    AlgebraicSpace.LocallyOfFiniteType (AlgebraicGeometry.AlgebraicStack.Isom.isomOverHom x y))
