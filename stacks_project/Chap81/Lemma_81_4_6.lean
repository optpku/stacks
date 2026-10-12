/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap73.Definition_73_7_1_FppfCover
public import stacks_project.Chap81.Lemma_81_4_2_Pseudofunctor

/-!
# Lemma 81.4.6

An fppf covering of algebraic spaces satisfies descent for Type-valued sheaves
on the small étale site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.EtaleSheaf

/-- Lemma 81.4.6: Let `S` be a scheme. Let `{f i : Xᵢ i ⟶ X}` be an fppf covering
of algebraic spaces over `S`. The functor from Type-valued sheaves on the small
étale site of `X` to descent data for étale sheaves along that family is an
equivalence of categories. -/
@[stacks 0GFX]
theorem descentIsEquivalenceOfFppfCovering
    {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    {Xᵢ : ι → AlgebraicSpace S} (f : ∀ i, Xᵢ i ⟶ X) [FppfCovering Xᵢ f] :
    (pseudofunctor.toDescentData f).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.EtaleSheaf
