/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiFinite.Composition
import StacksCheckRecall

/-!
# Composition of quasi-finite morphisms of algebraic stacks

A composition of quasi-finite morphisms of algebraic stacks is quasi-finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

/- Lemma 101.24.2: A composition of quasi-finite morphisms is quasi-finite.

Stacks writes the composition as `g ∘ f`; the Lean composite is `f ≫ g`. -/
@[stacks 0G2N] #check (AlgebraicGeometry.AlgebraicStack.QuasiFinite.comp :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [AlgebraicStack.QuasiFinite f] [AlgebraicStack.QuasiFinite g],
    AlgebraicStack.QuasiFinite (f ≫ g))
