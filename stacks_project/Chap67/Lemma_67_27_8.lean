/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.27.8: if `g ∘ f` is locally quasi-finite then so is `f`. -/
@[stacks 03XN] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [LocallyQuasiFinite (f ≫ g)], LocallyQuasiFinite f)
