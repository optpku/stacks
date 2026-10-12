/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap03.Lemma_3_11_1_Cardinal
public import ReasLib.CategoryTheory.Sites.Family.Covering
public import ReasLib.CategoryTheory.Sites.Precoverage.Combinatorial

@[expose] public section

universe u v w

noncomputable section

open CategoryTheory
open SemiRepresentableFamily.Over
open scoped Cardinal

namespace CategoryTheory.Precoverage

variable {C : Type u} [Category.{v} C]

/-- A rank-aware truncation models the source's `Cov(C)_{κ, α}`: `rank` is the
set-coded rank of a covering presieve, while `κ` bounds its raw indexed support. -/
def restrictCardinalRankLE (J : Precoverage C)
    (rank : ∀ {X : C}, Presieve X → Ordinal.{max u v w})
    (κ : Cardinal.{max u v w}) (α : Ordinal.{max u v w}) : Precoverage C where
  coverings X :=
    {R | R ∈ J X ∧ rank R < α ∧
      Cardinal.lift.{max u v w} #(R.uncurry) ≤ Cardinal.lift.{max u v} κ}

/-- Membership in the cardinal-and-rank truncation is its ambient covering,
rank, and raw-support conditions. -/
theorem mem_restrictCardinalRankLE_iff (J : Precoverage C)
    (rank : ∀ {X : C}, Presieve X → Ordinal.{max u v w})
    (κ : Cardinal.{max u v w}) (α : Ordinal.{max u v w})
    {X : C} {R : Presieve X} :
    R ∈ J.restrictCardinalRankLE rank κ α X ↔
      R ∈ J X ∧ rank R < α ∧
        Cardinal.lift.{max u v w} #(R.uncurry) ≤ Cardinal.lift.{max u v} κ := by
  rfl

/-- Lemma 3.11.1. A set of covering families in a site is contained in a
cardinal- and limit-ordinal-bounded subsite, and every ambient covering is
combinatorially equivalent to one in that subsite. -/
@[stacks 000X]
theorem exists_cardinalLE_site (J : Precoverage C) [J.IsSite]
    (rank : ∀ {X : C}, Presieve X → Ordinal.{max u v w})
    (Cov0 : Set (Σ X : C, SemiRepresentableFamily.Over.{w} X))
    (hCov0 : ∀ 𝒰 ∈ Cov0, IsCovering J 𝒰.2) :
    ∃ κ : Cardinal.{max u v w}, ∃ α : Ordinal.{max u v w}, Order.IsSuccLimit α ∧
      (∀ 𝒰 ∈ Cov0,
        IsCovering (J.restrictCardinalRankLE rank κ α) 𝒰.2 ∧
          Cardinal.lift.{max u v w} #(𝒰.2.index) ≤ Cardinal.lift.{w} κ) ∧
      (J.restrictCardinalRankLE rank κ α).IsSite ∧
      J.coversUpToCombinatorialEquivalence (J.restrictCardinalRankLE rank κ α) :=
  sorry

/-- A sub-precoverage seed is contained in some infinite-cardinal site truncation of `J`
that still combinatorially represents every `J`-covering. -/
theorem exists_cardinalLE_site_of_le (J : Precoverage C) [J.IsSite]
    (J0 : Precoverage C) (hJ0 : J0 ≤ J) :
    ∃ κ : Cardinal.{max u v},
      J0 ≤ J.restrictCardinalLE κ ∧
      (J.restrictCardinalLE κ).IsSite ∧
      J.coversUpToCombinatorialEquivalence (J.restrictCardinalLE κ) :=
  sorry

end CategoryTheory.Precoverage
