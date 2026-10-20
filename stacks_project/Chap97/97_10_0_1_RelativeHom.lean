/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom
public import stacks_project.Chap65.Lemma_65_7_3_Pullback

/-!
# Relative morphisms of algebraic spaces

The relative-morphism pair API is provided by the reusable algebraic-space owner.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.Pair :
  ∀ {S : Scheme.{u}} {B Z X : AlgebraicSpace S},
    (Z ⟶ B) → (X ⟶ B) → Over S → Type (u + 1))
