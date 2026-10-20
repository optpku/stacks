/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 67.30.1 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is flat if the equivalent conditions of Lemma 67.22.1 hold with `P` = flat. -/
@[stacks 03ML] #check (AlgebraicGeometry.AlgebraicSpace.Flat :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y), Prop)

/- Definition 67.30.1 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is flat at a point `x` of `|X|` (`Points X`) if the equivalent conditions of
Lemma 67.22.5 hold with `Q` = induced map of local rings is flat. This is
well-defined by Lemma 35.33.4. -/
@[stacks 03ML] #check (AlgebraicGeometry.AlgebraicSpace.FlatAt :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y) (x : AlgebraicGeometry.AlgebraicSpace.Points X), Prop)
