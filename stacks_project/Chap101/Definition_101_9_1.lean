/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Morphism.Affine
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 101.9.1: a morphism `f : X ⟶ Y` of algebraic stacks is affine
if it is representable by algebraic spaces and affine in the sense of
Section 100.3, i.e. `has (@AlgebraicSpace.Affine S) f`. -/
@[stacks 0CHQ] #check (AlgebraicGeometry.Groupoids.Hom.Affine :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.GroupoidsOver S},
    (X ⟶ Y) → Prop)
