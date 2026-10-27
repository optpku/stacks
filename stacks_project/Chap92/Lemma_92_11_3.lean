/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.NaiveComparison.IsIso
import StacksCheckRecall

/-!
# Comparison of the truncated cotangent complex with the naive cotangent complex

Lemma 92.11.3 records that the canonical morphism `toTruncGE_self` of 92.11.1.2,
attached to the self-presentation `A[B] ⟶ B`, is an isomorphism in `D(B)`.
-/

@[expose] public section

open CategoryTheory

universe u

noncomputable section

namespace Algebra.NaiveCotangent

/- Lemma 92.11.3. -/
@[stacks 08RB] #check (Algebra.NaiveCotangent.toTruncGE_self_isIso :
  ∀ (A : CommRingCat.{u}) (B : CategoryTheory.Under A),
    CategoryTheory.IsIso (Algebra.NaiveCotangent.toTruncGE_self A B))

end Algebra.NaiveCotangent
