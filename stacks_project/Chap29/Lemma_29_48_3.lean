/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/-!
# Lemma 29.48.3

The reusable composition API is maintained in
`ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations`.
-/

/- Lemma 29.48.3: finite locally free scheme morphisms are closed under composition. -/
@[stacks 02KC] #check (AlgebraicGeometry.IsFiniteLocallyFree.comp :
  ∀ {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z},
    IsFiniteLocallyFree f → IsFiniteLocallyFree g → IsFiniteLocallyFree (f ≫ g))
