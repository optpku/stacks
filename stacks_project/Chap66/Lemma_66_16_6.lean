/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap66.Lemma_66_16_6_Postcomp
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/- Lemma 66.16.6: let `S` be a scheme, let `X`, `Y`, `Z` be algebraic spaces over `S`,
let `g : X ⟶ Z` and `h : Y ⟶ Z` be étale, and let `f : X ⟶ Y` satisfy `f ≫ h = g`.
Then `f` is étale. -/
@[stacks 03FV] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.of_comp_eq :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (g : X ⟶ Z) (h : Y ⟶ Z) (f : X ⟶ Y)
      [AlgebraicSpace.Etale g] [AlgebraicSpace.Etale h] (_ : f ≫ h = g), AlgebraicSpace.Etale f)
