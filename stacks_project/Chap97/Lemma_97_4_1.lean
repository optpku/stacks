/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Cancellation
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

/- Lemma 97.4.1: let `X ⟶ Y ⟶ Z` be 1-morphisms of categories fibred in
groupoids over `(Sch/S)_fppf`. If `X ⟶ Z` and `Y ⟶ Z` are representable by
algebraic spaces and étale, so is `X ⟶ Y`. Here `Hom.Etale` packages
representability by algebraic spaces and étale. -/
@[stacks 05XK] #check
  (AlgebraicGeometry.Groupoids.Hom.Etale.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [AlgebraicGeometry.Groupoids.Hom.Etale (f ≫ g)]
      [AlgebraicGeometry.Groupoids.Hom.Etale g],
      AlgebraicGeometry.Groupoids.Hom.Etale f)
