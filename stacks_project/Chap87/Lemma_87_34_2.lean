module

import stacks_project.Chap07.Definition_7_14_1
public import stacks_project.Chap87.Lemma_87_34_2_Pullback
public import stacks_project.Chap87.Lemma_87_34_2_Topos
import StacksCheckRecall

/-!
# Lemma 87.34.2

A morphism of formal algebraic spaces induces a morphism of étale sites of
algebraic spaces over the reductions, hence a morphism of small étale topoi.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 87.34.2 (1): a morphism `f : X ⟶ Y` of formal algebraic spaces over a
scheme `S` induces a continuous functor `Y_spaces,étale ⥤ X_spaces,étale`,
hence a morphism of sites
`f_spaces,étale : X_spaces,étale ⟶ Y_spaces,étale`. -/
@[stacks 0DEC] #check
  (spacesEtalePullback_isMorphismOfSites :
    ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
      [Reduction X] [Reduction Y] (f : X ⟶ Y),
      IsMorphismOfSites (spacesEtaleTopology Y) (spacesEtaleTopology X)
        (spacesEtalePullback f))

/- Lemma 87.34.2 (2): the rule `f ↦ f_spaces,étale` is compatible with
composition, as the algebraic-space pullback-composition isomorphism along
`mapReduction`, in the sense of Sites, Definition 7.14.5. -/
@[stacks 0DEC] #check
  (spacesEtalePullbackComp :
    ∀ {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
      [IsFormalAlgebraicSpace Z] [Reduction X] [Reduction Y] [Reduction Z]
      (f : X ⟶ Y) (g : Y ⟶ Z),
      AlgebraicSpace.spacesEtalePullback (mapReduction f ≫ mapReduction g) ≅
        spacesEtalePullback g ⋙ spacesEtalePullback f)

#check CategoryTheory.IsExactMorphismOfSites.comp

/- Lemma 87.34.2 (3): transporting the topos morphism of `f_spaces,étale` along
equation 87.34.1.1 yields `f_small : Sh(X_étale) ⟶ Sh(Y_étale)`, compatible
with composition. -/
@[stacks 0DEC] #check
  (smallEtaleMorphismOfTopoi :
    ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
      [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
      [Reduction X] [Reduction Y],
      (X ⟶ Y) →
        MorphismOfTopoiIn (smallEtaleTopology Y) (smallEtaleTopology X))

#check smallEtaleMorphismOfTopoiComp
