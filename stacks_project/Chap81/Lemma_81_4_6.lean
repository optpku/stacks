/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.FppfDescent
import StacksCheckRecall

/-!
# Lemma 81.4.6

An fppf covering of algebraic spaces satisfies descent for Type-valued sheaves
on the small étale site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

/- Lemma 81.4.6: Let `S` be a scheme. Let `{f i : Xᵢ i ⟶ X}` be an fppf covering
of algebraic spaces over `S`. The functor from Type-valued sheaves on the small
étale site of `X` to descent data for étale sheaves along that family is an
equivalence of categories. -/
@[stacks 0GFX] #check
  (AlgebraicGeometry.AlgebraicSpace.EtaleSheaf.descentIsEquivalenceOfFppfCovering :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
      {Xᵢ : ι → AlgebraicSpace S} (f : ∀ i, Xᵢ i ⟶ X) [FppfCovering Xᵢ f],
      (AlgebraicGeometry.AlgebraicSpace.EtaleSheaf.pseudofunctor.toDescentData f).IsEquivalence)
