/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian.LimitPreserving
import StacksCheckRecall

/-!
# Lemma 98.25.2

Restricting along the inclusion `(Noetherian/S)_τ ⟶ (Sch/S)_τ` is an
equivalence between the categories of limit-preserving sheaves on these
two sites.
-/

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 98.25.2: restriction to locally Noetherian schemes over a locally
Noetherian base is an equivalence for each of the five standard topologies. -/
@[stacks 0GE3] #check
  (AlgebraicGeometry.StandardTopology.restrictLimitPreservingSheaf_isEquivalence :
    ∀ (τ : StandardTopology) (S : Scheme.{u}) [IsLocallyNoetherian S],
      (AlgebraicGeometry.StandardTopology.restrictLimitPreservingSheaf τ S).IsEquivalence)
