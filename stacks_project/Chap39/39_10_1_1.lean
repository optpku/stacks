/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import ReasLib.CategoryTheory.Monoidal.Mod
import StacksCheckRecall

universe u

open AlgebraicGeometry CategoryTheory MonoidalCategory MonObj

variable (S : Scheme.{u}) (G : Grp (Over S)) (X : Over S) (A : ModObj G.X X)

/- 39.10.1.1: An action of the group scheme `G` on `X` is a morphism
`G.X ⊗ X ⟶ X` compatible with multiplication and the identity of `G`, as expressed by
the associativity square and unit triangle. -/
@[stacks 03LD] #check
  (CategoryTheory.ModObj.laws G.X X A :
    (μ[G.X] ▷ X) ≫ A.smul = (α_ G.X G.X X).hom ≫ (G.X ◁ A.smul) ≫ A.smul ∧
      (η[G.X] ▷ X) ≫ A.smul = (λ_ X).hom)
