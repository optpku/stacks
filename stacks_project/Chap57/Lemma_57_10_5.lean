/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded.NegativeObjects
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u

/-Lemma 57.10.5: Let `𝒜` be an abelian category with enough negative objects.
For a morphism `f : X ⟶ X'` in `Dᵇ(𝒜)`, with `Hⁱ(X) = 0` for `b < i` and
`Hⁱ(X') = 0` for `b ≤ i`, there exist `N` and
`g : (DerivedCategory.Bounded.singleFunctor C b).obj N ⟶ X` such that
`topCohomologyMap b X g` is epi, every map
`(DerivedCategory.Bounded.homologyFunctor C b).obj X ⟶ N` is zero, and
`g ≫ f = 0`. -/
@[stacks 0GWG] #check
  (CategoryTheory.DerivedCategory.Bounded.exists_shifted_map_with_zero_comp :
    ∀ {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C],
      HasEnoughNegativeObjects C →
        ∀ (X X' : DerivedCategory.Bounded C) (f : X ⟶ X') (b : ℤ),
          (∀ i : ℤ, b < i →
            IsZero ((DerivedCategory.Bounded.homologyFunctor C i).obj X)) →
          (∀ i : ℤ, b ≤ i →
            IsZero ((DerivedCategory.Bounded.homologyFunctor C i).obj X')) →
          ∃ (N : C)
            (g : (DerivedCategory.Bounded.singleFunctor C b).obj N ⟶ X),
            Epi (CategoryTheory.DerivedCategory.Bounded.topCohomologyMap b X g) ∧
              (∀ h : (DerivedCategory.Bounded.homologyFunctor C b).obj X ⟶ N,
                h = 0) ∧
                g ≫ f = 0)
