/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.IndexedSite.SetFamily
public import ReasLib.CategoryTheory.Sites.Family.Covering
public import Mathlib.SetTheory.ZFC.Cardinal
public import Mathlib.SetTheory.ZFC.Rank
public import Mathlib.SetTheory.ZFC.VonNeumann

/-!
# Cardinal and rank bounds on indexed sites

A relatively small collection of coverings can be retained in a site bounded simultaneously
by the cardinality of its index sets and the von Neumann rank of its encoded families.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.SetIndexedFamily

variable {C : Type u} [Category.{v} C]

/-- The coverings whose complete family codes have rank below `α` and whose index sets
have cardinality at most `κ`. -/
def restrictCardinalRank (Cov : ∀ target : C, Set (SetIndexedFamily.{w} target))
    (κ : Cardinal.{max u v w}) (α : Ordinal.{max u v w})
    (target : C) : Set (SetIndexedFamily.{w} target) :=
  {F | F ∈ Cov target ∧ F.code.rank < α ∧ F.indexSet.card ≤ κ}

/-- Membership in a cardinal and rank truncation is precisely the ambient covering condition
together with the rank and index-cardinality bounds. -/
theorem mem_restrictCardinalRank_iff
    (Cov : ∀ target : C, Set (SetIndexedFamily.{w} target))
    (κ : Cardinal.{max u v w}) (α : Ordinal.{max u v w})
    {target : C} {F : SetIndexedFamily.{w} target} :
    F ∈ restrictCardinalRank Cov κ α target ↔
      F ∈ Cov target ∧ F.code.rank < α ∧ F.indexSet.card ≤ κ := by
  rfl

/-- Every relatively small collection of coverings in an indexed site is contained in a
cardinal and limit-rank truncation which is itself a site and combinatorially represents
every ambient covering. -/
theorem exists_cardinalRank_site
    (Cov : ∀ target : C, Set (SetIndexedFamily.{w} target))
    (hCov : IsSite Cov)
    (Cov0 : Set (Σ target : C, SetIndexedFamily.{w} target))
    [Small.{max u v w} Cov0]
    (hCov0 : ∀ F ∈ Cov0, F.2 ∈ Cov F.1) :
    ∃ κ : Cardinal.{max u v w}, ∃ α : Ordinal.{max u v w}, Order.IsSuccLimit α ∧
      (∀ F ∈ Cov0, F.2 ∈ restrictCardinalRank Cov κ α F.1) ∧
      IsSite (restrictCardinalRank Cov κ α) ∧
      (∀ (target : C) (F : SetIndexedFamily.{w} target), F ∈ Cov target →
        ∃ G : SetIndexedFamily.{w} target, G ∈ restrictCardinalRank Cov κ α target ∧
          SemiRepresentableFamily.Over.CombinatoriallyEquivalent F.toFamily G.toFamily) :=
  sorry

end CategoryTheory.SetIndexedFamily
