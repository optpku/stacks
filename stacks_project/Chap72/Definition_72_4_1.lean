/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap72.Definition_72_4_1_Integral
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 72.4.1: an algebraic space `X` over a scheme `S` is integral if it is
reduced, decent, and `|X|` is irreducible. -/
@[stacks 0AD4] #check (AlgebraicGeometry.AlgebraicSpace.isIntegral_iff :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    IsIntegral X ↔ IsReduced X ∧ IsDecent X ∧ IsIrreducible X)
