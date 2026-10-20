/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Isom.Group
import StacksCheckRecall

/-!
# Lemma 101.3.2

For an algebraic stack `X` and fibre objects `x, y` over a scheme `T`,
`Isom_X(y, y)` is a group algebraic space over `T`, and `Isom_X(x, y)` is a
pseudo torsor for that group space over `T`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids

universe u

/- Lemma 101.3.2 (1): `Isom_X(y, y)` is a group algebraic space over `T`. -/
@[stacks 04YP]
#check (AlgebraicGeometry.AlgebraicStack.Isom.automorphismGroup_X :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (y : X.p.Fiber T),
    (AlgebraicGeometry.AlgebraicStack.Isom.automorphismGroup y).X =
      AlgebraicGeometry.AlgebraicStack.Isom.isomOver y y)

/- Lemma 101.3.2 (2): `Isom_X(x, y)` is a pseudo torsor for `Isom_X(y, y)` over `T`. -/
@[stacks 04YP]
#check (AlgebraicGeometry.AlgebraicStack.Isom.instIsPseudoTorsor_action :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {T : Over S} (x y : X.p.Fiber T),
    Mod.IsPseudoTorsor (AlgebraicGeometry.AlgebraicStack.Isom.action x y))
