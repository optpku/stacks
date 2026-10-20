/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth.Flat
import StacksCheckRecall

/-!
# Smooth morphisms of algebraic spaces are flat
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.37.7: A smooth morphism of algebraic spaces is flat. -/
@[stacks 04TA] #check (AlgebraicGeometry.AlgebraicSpace.Smooth.flat :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.Smooth f],
    AlgebraicGeometry.AlgebraicSpace.Flat f)
