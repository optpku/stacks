module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.GerbeMorphism
public import stacks_project.Chap78.Lemma_78_15_1_Action
public import stacks_project.Chap78.Lemma_78_20_2_Atlas
public import stacks_project.Chap78.Lemma_78_27_2_TrivialAction

/-!
# The classifying morphism of a group algebraic space is a gerbe

This file records that the canonical morphism `[B/G] ⟶ 𝒮_B` of Lemma 78.20.2
exhibits the quotient stack of the trivial `G`-action on `B` as a gerbe over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidAlgebraicSpace AlgebraicGeometry.GroupAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Lemma 78.27.2. Let `S` be a scheme. Let `B` be an algebraic space over `S`. Let
`G` be a group algebraic space over `B`. Endow `B` with the trivial action of `G`.
The morphism `[B/G] ⟶ 𝒮_B` of Lemma 78.20.2 turns `[B/G]` into a gerbe over `B`.
Here `[B/G]` is `(ofAction G (trivialAction G)).quotientStack`, `𝒮_B` is
`stackInSets B`, and the morphism is `toBase (ofAction G (trivialAction G))`. -/
@[stacks 06PF]
theorem toBase_trivialAction_isGerbeMorphism {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) :
    CartesianBasedFunctor.IsGerbeMorphism (Scheme.fppfTopology.over S)
      (toBase (ofAction G (trivialAction G))) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
