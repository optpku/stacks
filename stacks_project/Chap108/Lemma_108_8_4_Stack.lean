/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.Stack

/-! # Picard stacks of morphisms of algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- The Picard projection is a stack in groupoids for the fppf topology. -/
#check (AlgebraicGeometry.AlgebraicSpace.Picard.isStackInGroupoids :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B),
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (Picard.p f))

/- The bundled Picard stack has the Picard category as its total category. -/
#check (AlgebraicGeometry.AlgebraicSpace.picardStack :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B),
    StackOver.Groupoids (Scheme.fppfTopology.over S))
