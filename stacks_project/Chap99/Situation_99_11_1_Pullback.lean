/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap99.Situation_99_11_1_PicardGroup

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.Pullback

/-! # Pullback on Picard groups of algebraic spaces -/

@[expose] public section

open CategoryTheory

universe u

/- A morphism induces the contravariant pullback homomorphism on Picard groups. -/
#check (AlgebraicGeometry.AlgebraicSpace.picardPullback :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → (Y.PicardGroup →+ X.PicardGroup))
