/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap91.«91_3_1_1_Arrow»
public import stacks_project.Chap91.«91_3_1_1_Thickening»
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

universe u

/- 91.3.1.1: a morphism of thickenings of ringed spaces is a commutative square
whose horizontal arrows are thickenings. -/
@[stacks 08L0] #check (AlgebraicGeometry.RingedSpace.Thickening.homMk :
  {T U : AlgebraicGeometry.RingedSpace.Thickening.{u}} →
    (f : T.left ⟶ U.left) → (f' : T.right ⟶ U.right) →
      f ≫ U.hom = T.hom ≫ f' → (T ⟶ U))
