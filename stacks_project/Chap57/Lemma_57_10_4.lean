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

/- Lemma 57.10.4: Let `𝒜` be an abelian category with enough negative objects.
For `X ∈ Dᵇ(𝒜)` whose cohomology vanishes above `b`, there are an object `N`
and a map `N[-b] ⟶ X` whose induced map `N ⟶ Hᵇ(X)` is an epimorphism and
for which every map `Hᵇ(X) ⟶ N` is zero. -/
@[stacks 0GWF] #check
  (CategoryTheory.DerivedCategory.Bounded.exists_shifted_map_with_surjective_top_cohomology :
    ∀ {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (hneg : HasEnoughNegativeObjects C) (X : DerivedCategory.Bounded C) (b : ℤ)
    (hvanish : ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.Bounded.homologyFunctor C i).obj X)),
    ∃ (N : C)
      (f : (DerivedCategory.Bounded.singleFunctor C b).obj N ⟶ X),
      Epi (DerivedCategory.Bounded.topCohomologyMap b X f) ∧
        ∀ g : (DerivedCategory.Bounded.homologyFunctor C b).obj X ⟶ N, g = 0)
