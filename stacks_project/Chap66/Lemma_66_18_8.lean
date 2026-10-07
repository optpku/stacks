module

public import stacks_project.Chap66.Lemma_66_18_8_Pullback
public import stacks_project.Chap66.Lemma_66_18_8_Representable
public import stacks_project.Chap66.Lemma_66_18_8_Topos
import StacksCheckRecall

/-!
# Lemma 66.18.8

A morphism of algebraic spaces induces a morphism of étale sites of algebraic spaces,
hence a morphism of small étale topoi; if the morphism is representable this comes from
a morphism of small étale sites.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 66.18.8 (1): the continuous functor `V ↦ X ×_Y V` on étale sites of algebraic
spaces induces a morphism of sites `f_spaces,étale : X_spaces,étale ⟶ Y_spaces,étale`. -/
@[stacks 03G2] #check
  (spacesEtalePullback_isMorphismOfSites :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      IsMorphismOfSites (spacesEtaleTopology Y) (spacesEtaleTopology X)
        (spacesEtalePullback f))

/- Lemma 66.18.8 (2): the rule `f ↦ f_spaces,étale` is compatible with composition. -/
@[stacks 03G2] #check
  (spacesEtalePullbackComp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z),
      spacesEtalePullback (f ≫ g) ≅ spacesEtalePullback g ⋙ spacesEtalePullback f)

#check CategoryTheory.IsMorphismOfSites.comp

/- Lemma 66.18.8 (3): transporting along Lemma 66.18.3 yields a morphism of topoi
`f_small : Sh(X_étale) ⟶ Sh(Y_étale)` compatible with composition. -/
@[stacks 03G2] #check
  (smallEtaleMorphismOfTopoi :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
      (X ⟶ Y) → MorphismOfTopoiIn (smallEtaleTopology Y) (smallEtaleTopology X))

#check smallEtaleMorphismOfTopoiComp

/- Lemma 66.18.8 (4): if `f` is representable, then `f_small` comes from the morphism of
small étale sites given by `V ↦ X ×_Y V`. -/
@[stacks 03G2] #check
  (smallEtalePullback_isMorphismOfSites :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      (hf : yoneda.relativelyRepresentable f),
      IsMorphismOfSites (smallEtaleTopology Y) (smallEtaleTopology X)
        (smallEtalePullback f hf))

#check smallEtalePullbackCompInclusion
