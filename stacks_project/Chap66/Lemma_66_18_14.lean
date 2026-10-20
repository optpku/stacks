module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AtlasDescent
import StacksCheckRecall

/-!
# Lemma 66.18.14

A sheaf on the small étale site of an algebraic space is equivalent to a sheaf
on a presenting atlas equipped with a cocycle isomorphism along the kernel pair.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory.Limits

universe u

/- Lemma 66.18.14 (1): for a sheaf F on X_étale, the inverse image
G = φ^{-1} F along a presenting atlas carries a canonical isomorphism
α : t^{-1} G ≅ s^{-1} G. -/
@[stacks 05YY] #check
  (AlgebraicGeometry.AlgebraicSpace.presentationInverseImageIso :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X),
      ∀ F : Sheaf (smallEtaleTopology X) (Type (u + 1)),
        (smallEtaleMorphismOfTopoi (relationT φ)).inverseImage.obj
            (presentationInverseImage φ F) ≅
          (smallEtaleMorphismOfTopoi (relationS φ)).inverseImage.obj
            (presentationInverseImage φ F))


/- Lemma 66.18.14 (cocycle): the canonical kernel-pair isomorphism satisfies
the cocycle identity on the composable-arrow pullback. -/
@[stacks 05YY] #check
  (AlgebraicGeometry.AlgebraicSpace.presentationInverseImageIso_cocycle :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
      (φ : ofOver U ⟶ X),
      ∀ F : Sheaf (smallEtaleTopology X) (Type (u + 1)),
        AlgebraicGeometry.AlgebraicSpace.presentationInverseImageIso_comp φ
            (AlgebraicGeometry.AlgebraicSpace.relationC φ) F =
          eqToIso
              (congrArg (fun h ↦
                (smallEtaleMorphismOfTopoi h).inverseImage.obj
                  (AlgebraicGeometry.AlgebraicSpace.presentationInverseImage φ F))
                (AlgebraicGeometry.AlgebraicSpace.relationC_comp_relationT φ)) ≪≫
            AlgebraicGeometry.AlgebraicSpace.presentationInverseImageIso_comp φ
              (AlgebraicGeometry.AlgebraicSpace.relationPr0 φ) F ≪≫
            eqToIso
              (congrArg (fun h ↦
                (smallEtaleMorphismOfTopoi h).inverseImage.obj
                  (AlgebraicGeometry.AlgebraicSpace.presentationInverseImage φ F))
                (pullback.condition :
                  AlgebraicGeometry.AlgebraicSpace.relationPr0 φ ≫
                      AlgebraicGeometry.AlgebraicSpace.relationS φ =
                    AlgebraicGeometry.AlgebraicSpace.relationPr1 φ ≫
                      AlgebraicGeometry.AlgebraicSpace.relationT φ)) ≪≫
            AlgebraicGeometry.AlgebraicSpace.presentationInverseImageIso_comp φ
              (AlgebraicGeometry.AlgebraicSpace.relationPr1 φ) F ≪≫
            eqToIso
              (congrArg (fun h ↦
                (smallEtaleMorphismOfTopoi h).inverseImage.obj
                  (AlgebraicGeometry.AlgebraicSpace.presentationInverseImage φ F))
                (AlgebraicGeometry.AlgebraicSpace.relationC_comp_relationS φ).symm))

/- Lemma 66.18.14 (2): the functor F ↦ (G, α) is an equivalence between sheaves
on X_étale and pairs (G, α) as above. -/
@[stacks 05YY] #check
  (AlgebraicGeometry.AlgebraicSpace.sheafToPresentationDescent_isEquivalence :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (φ : ofOver U ⟶ X)
      [Etale φ],
      Function.Surjective (Points.map φ) →
        (sheafToPresentationDescent φ).IsEquivalence)
