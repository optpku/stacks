/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Syntomic
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 67.36.1 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is syntomic if the equivalent conditions of Lemma 67.22.1 hold with `P` = syntomic. -/
@[stacks 03Z7] #check (AlgebraicGeometry.AlgebraicSpace.Syntomic :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y), Prop)

/- Definition 67.36.1 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is syntomic at a point `x` of `|X|` if some open neighbourhood `X' ⊂ X` of `x` has
syntomic restriction `f|_{X'} : X' ⟶ Y`. -/
@[stacks 03Z7] #check (AlgebraicGeometry.AlgebraicSpace.SyntomicAt :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y) (x : AlgebraicGeometry.AlgebraicSpace.Points X), Prop)
