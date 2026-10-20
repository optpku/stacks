/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.Square
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- 38.5.7.1: a pointed elementary étale refinement square over a morphism of schemes. -/
@[stacks 05HS] #check
  (AlgebraicGeometry.Scheme.EtaleNeighborhood.Elementary.RefinementSquare :
    ∀ {Y S : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ S) (y : Y), Type (u + 1))
