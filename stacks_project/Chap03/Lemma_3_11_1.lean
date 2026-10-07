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

/-- Lemma 3.11.1. Given a site precoverage `J` and a set `Cov0` of `J`-covering families
whose index cardinals are bounded by a cardinal `μ`, there exists a cardinal `κ` such
that every family in `Cov0` remains covering for `J.restrictCardinalLE κ` with index
cardinality at most `κ`, this truncation is a site, and every `J`-covering is
combinatorially equivalent to a covering of the truncation.
The source's limit ordinal α is omitted as a rank cut: Lean presieves are already sets.
The seed bound `μ` records that a ZFC set of families has a supremum of index cardinals. -/
@[stacks 000X]
theorem exists_cardinalLE_site (J : Precoverage C) [J.IsSite]
    (Cov0 : Set (Σ X : C, SemiRepresentableFamily.Over.{w} X))
    (hCov0 : ∀ 𝒰 ∈ Cov0, IsCovering J 𝒰.2)
    (μ : Cardinal.{max u v w})
    (hμ : ∀ 𝒰 ∈ Cov0, Cardinal.lift.{max u v w} #(𝒰.2.index) ≤ Cardinal.lift.{w} μ) :
    ∃ κ : Cardinal.{max u v w},
      (∀ 𝒰 ∈ Cov0,
        IsCovering (J.restrictCardinalLE κ) 𝒰.2 ∧
          Cardinal.lift.{max u v w} #(𝒰.2.index) ≤ Cardinal.lift.{w} κ) ∧
      (J.restrictCardinalLE κ).IsSite ∧
      J.coversUpToCombinatorialEquivalence (J.restrictCardinalLE κ) :=
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
