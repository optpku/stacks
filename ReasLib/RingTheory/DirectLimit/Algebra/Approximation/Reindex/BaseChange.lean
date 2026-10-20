/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.BaseChange.Properties
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Reindex.Core
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change under reindexing

This leaf records the stage base-change computation after an order-isomorphic
change of indices.  The data-only reindexing API remains available without the
base-change import.
-/

@[expose] public section

universe u v w x

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation.Hom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- Reindexing only changes the names of the stages in a base-change map. -/
@[simp, stacks 00R1 "reindexed directed approximation base change"]
theorem reindex_baseChangeMap (A : Hom f) {J : Type x}
    [Preorder J] (e : J ≃o A.index) {j k : J} (h : j ≤ k) :
    (A.reindex e).baseChangeMap h =
      A.baseChangeMap (e.monotone h) := sorry

/-- Surjectivity of all stage base-change maps is invariant under an
order-isomorphic change of stages. -/
@[stacks 00R1 "reindexed directed approximation base change"]
theorem reindex_baseChange_surjective (A : Hom f)
    (hA : A.baseChange_surjective) {J : Type x} [Preorder J]
    (e : J ≃o A.index) :
    (A.reindex e).baseChange_surjective := sorry

/-- Injectivity of all stage base-change maps is invariant under an
order-isomorphic change of stages. -/
@[stacks 00R1 "reindexed directed approximation base change"]
theorem reindex_baseChange_injective (A : Hom f)
    (hA : A.baseChange_injective) {J : Type x} [Preorder J]
    (e : J ≃o A.index) :
    (A.reindex e).baseChange_injective := sorry

/-- Bijectivity of all stage base-change maps is invariant under an
order-isomorphic change of stages. -/
@[stacks 00R1 "reindexed directed approximation base change"]
theorem reindex_baseChange_bijective (A : Hom f)
    (hA : A.baseChange_bijective) {J : Type x} [Preorder J]
    (e : J ≃o A.index) :
    (A.reindex e).baseChange_bijective := sorry

/-- The localization-of-quotient transition property is invariant under an
order-isomorphic change of stages. -/
@[stacks 00R1 "reindexed directed approximation base change"]
theorem reindex_baseChange_isLocalizationOfQuotient (A : Hom f)
    (hA : A.baseChange_isLocalizationOfQuotient) {J : Type x}
    [Preorder J] (e : J ≃o A.index) :
    (A.reindex e).baseChange_isLocalizationOfQuotient := sorry

/-- Prime-localization transition witnesses are invariant under an
order-isomorphic change of stages. -/
@[stacks 00R1 "reindexed directed approximation base change"]
theorem reindex_baseChange_isLocalizationAtPrime (A : Hom f)
    (hA : A.baseChange_isLocalizationAtPrime) {J : Type x}
    [Preorder J] (e : J ≃o A.index) :
    (A.reindex e).baseChange_isLocalizationAtPrime := sorry

end Ring.DirectLimit.Algebra.Approximation.Hom
