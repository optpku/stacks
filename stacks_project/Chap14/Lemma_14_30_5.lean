/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import ReasLib.CategoryTheory.MorphismProperty.LiftingProperty.Sequence
import StacksCheckRecall

/-!
@stack 08NQ

# Lemma 14.30.5 compatibility facade

The reusable theorem handles every stage of an inverse sequence for the right lifting property of
an arbitrary morphism property. The source statement specializes it to the initial stage and the
boundary-inclusion property `I`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open SSet.modelCategoryQuillen

universe u

variable {X : ℕ → SSet.{u}} (f : ∀ n : ℕ, X (n + 1) ⟶ X n)

/- Lemma 14.30.5: the inverse-limit projection to the initial stage of a tower of trivial Kan
fibrations is again a trivial Kan fibration. -/
@[stacks 08NQ]
#check (CategoryTheory.MorphismProperty.rlp.limitProjection I f 0 :
  (∀ n : ℕ, I.rlp (f n)) →
    I.rlp (limit.π (Functor.ofOpSequence f) (Opposite.op 0)))
