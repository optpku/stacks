/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap99.Situation_99_11_1_Functor
public import stacks_project.Chap99.Situation_99_11_1_PicardGroup
public import stacks_project.Chap99.Situation_99_11_1_Pullback

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.Relative
import StacksCheckRecall

/-! # The Picard functor of a morphism of algebraic spaces -/

@[expose] public section

open CategoryTheory

universe u

/- Situation 99.11.1: for a morphism of algebraic spaces over a scheme, the
relative Picard functor is the fppf sheafification of the presheaf sending a
scheme over the base to the Picard group of its fiber. -/
@[stacks 0D25] #check (AlgebraicGeometry.AlgebraicSpace.picardFunctor :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X B : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ B) → CategoryTheory.Sheaf
      (AlgebraicGeometry.AlgebraicSpace.SchemesOver.fppfTopology B) (Type (u + 1)))
