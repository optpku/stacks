/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.FormallyEtale
import StacksCheckRecall

/-!
# Universal first-order thickenings over formally étale morphisms

A universal first-order thickening of `Z` over `Y` remains a universal
first-order thickening of `Z` over `X` after postcomposition with a
formally étale morphism `Y ⟶ X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.15.2: Let `S` be a scheme. Let `Z ⟶ Y ⟶ X` be morphisms of
algebraic spaces over `S`. If `i : Z ⟶ Z'` is a universal first-order
thickening of `Z` over `Y` via `g : Z' ⟶ Y` and `f : Y ⟶ X` is formally
étale, then `i` is a universal first-order thickening of `Z` over `X`
via `g ≫ f`. -/
@[stacks 0604] #check
  (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.of_formallyEtale :
    ∀ {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
      (i : Z ⟶ Z') (g : Z' ⟶ Y) (f : Y ⟶ X),
      [AlgebraicSpace.IsUniversalFirstOrder i g] → [AlgebraicSpace.FormallyEtale f] →
        AlgebraicSpace.IsUniversalFirstOrder i (g ≫ f))
