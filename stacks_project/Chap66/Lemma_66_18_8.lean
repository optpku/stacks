module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.RepresentablePullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesTopos
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
  (AlgebraicGeometry.AlgebraicSpace.spacesEtalePullback_isMorphismOfSites :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      IsMorphismOfSites (spacesEtaleTopology Y) (spacesEtaleTopology X)
        (spacesEtalePullback f))

/- Lemma 66.18.8 (2): the rule `f ↦ f_spaces,étale` is compatible with composition. -/
@[stacks 03G2] #check
  (AlgebraicGeometry.AlgebraicSpace.spacesEtalePullbackComp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z),
      spacesEtalePullback (f ≫ g) ≅ spacesEtalePullback g ⋙ spacesEtalePullback f)

/- Lemma 66.18.8 (3): transporting along Lemma 66.18.3 yields a morphism of topoi
`f_small : Sh(X_étale) ⟶ Sh(Y_étale)` compatible with composition. -/
@[stacks 03G2] #check
  (AlgebraicGeometry.AlgebraicSpace.smallEtaleMorphismOfTopoi :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
      (X ⟶ Y) → MorphismOfTopoiIn (smallEtaleTopology Y) (smallEtaleTopology X))

#check
  (AlgebraicGeometry.AlgebraicSpace.smallEtaleMorphismOfTopoiComp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z),
      (smallEtaleMorphismOfTopoi (f ≫ g)).inverseImage ≅
        ((smallEtaleMorphismOfTopoi g).comp (smallEtaleMorphismOfTopoi f)).inverseImage)

/- Lemma 66.18.8 (4): if `f` is representable, then `f_small` comes from the morphism of
small étale sites given by `V ↦ X ×_Y V`. -/
@[stacks 03G2] #check
  (AlgebraicGeometry.AlgebraicSpace.smallEtalePullback_isMorphismOfSites :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      (hf : yoneda.relativelyRepresentable f),
      IsMorphismOfSites (smallEtaleTopology Y) (smallEtaleTopology X)
        (smallEtalePullback f hf))

#check
  (AlgebraicGeometry.AlgebraicSpace.smallEtalePullbackCompInclusion :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      (hf : yoneda.relativelyRepresentable f),
      smallEtalePullback f hf ⋙ smallEtaleToSpaces X ≅
        smallEtaleToSpaces Y ⋙ spacesEtalePullback f)

#check
  (AlgebraicGeometry.AlgebraicSpace.smallEtaleMorphismOfTopoiRepresentableInverseImageIso :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      (hf : yoneda.relativelyRepresentable f),
      (smallEtaleMorphismOfTopoi f).inverseImage ≅
        (smallEtalePullback f hf).sheafPullback (Type (u + 1))
          (smallEtaleTopology Y) (smallEtaleTopology X))
