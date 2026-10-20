module

public import ReasLib.CategoryTheory.Sites.IndexedSite.CardinalRank
public import ReasLib.CategoryTheory.Sites.Precoverage.Cardinality
public import ReasLib.CategoryTheory.Sites.Precoverage.Combinatorial
import StacksCheckRecall

@[expose] public section

universe u v w

open CategoryTheory
open CategoryTheory.SetIndexedFamily

/- 000X::statement_repair::1
Lemma 3.11.1. A set of covering families in an indexed site is contained in a
cardinal- and limit-ordinal-bounded subsite, and every ambient covering is
combinatorially equivalent to one in that subsite.
-/
@[stacks 000X] #check (CategoryTheory.SetIndexedFamily.exists_cardinalRank_site :
  ∀ {C : Type u} [Category.{v} C]
    (Cov : ∀ target : C, Set (SetIndexedFamily.{w} target)),
    IsSite Cov →
    ∀ (Cov0 : Set (Σ target : C, SetIndexedFamily.{w} target))
      [Small.{max u v w} Cov0],
      (∀ F ∈ Cov0, F.2 ∈ Cov F.1) →
      ∃ κ : Cardinal.{max u v w}, ∃ α : Ordinal.{max u v w}, Order.IsSuccLimit α ∧
        (∀ F ∈ Cov0, F.2 ∈ restrictCardinalRank Cov κ α F.1) ∧
        IsSite (restrictCardinalRank Cov κ α) ∧
        (∀ (target : C) (F : SetIndexedFamily.{w} target), F ∈ Cov target →
          ∃ G : SetIndexedFamily.{w} target, G ∈ restrictCardinalRank Cov κ α target ∧
            SemiRepresentableFamily.Over.CombinatoriallyEquivalent F.toFamily G.toFamily))
