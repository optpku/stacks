/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.Existence
import StacksCheckRecall

/-!
# Existence of universal first-order thickenings

A formally unramified morphism of algebraic spaces over a scheme admits a
universal first-order thickening.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.15.4: Let `S` be a scheme. Let `h : Z ⟶ X` be a formally unramified
morphism of algebraic spaces over `S`. There exists a universal first-order
thickening of `Z` over `X`, i.e. algebraic spaces and morphisms
`i : Z ⟶ Z'` and `f : Z' ⟶ X` with `i ≫ f = h` such that
`IsUniversalFirstOrder i f`. -/
@[stacks 0606] #check
  (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.exists_of_formallyUnramified :
    ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (h : Z ⟶ X) [FormallyUnramified h],
      ∃ (Z' : AlgebraicSpace S) (i : Z ⟶ Z') (f : Z' ⟶ X),
        i ≫ f = h ∧ IsUniversalFirstOrder i f)
