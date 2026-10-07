module

import StacksCheckRecall
public import stacks_project.Chap73.Lemma_73_4_8_Identity

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
open Etale.SpacesToBig

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- Compatibility name for the identity-base spaces-étale to big-étale site morphism. -/
noncomputable abbrev spacesEtaleToOverEtaleSiteMorphismOfTopoi
    [HasWeakSheafify (overEtaleTopology X) (Type (u + 1))] :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u + 1}
      (spacesEtaleTopology X) (overEtaleTopology X) :=
  siteMorphismOfTopoi.{u, u + 1} X

/- Lemma 73.4.8 (1): the identity-base relocalization functor defines a morphism
of spaces-étale to big étale sites. -/
@[stacks 0DF3] #check
  (identity_isMorphismOfSites X :
    IsMorphismOfSites (spacesEtaleTopology X) (overEtaleTopology X)
      (relocalizationFunctor (𝟙 X)))

/- Lemma 73.4.8 (2): the identity-base site morphism induces the morphism of
topoi `π_X`. -/
@[stacks 0DF3] #check
  (siteMorphismOfTopoi.{u, u + 1} X :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u + 1}
      (spacesEtaleTopology X) (overEtaleTopology X))

/- Lemma 73.4.8 (3): the site-induced morphism `π_X` composed with
`i_X = i_{𝟙 X}` is the identity on the spaces-étale topos. -/
@[stacks 0DF3] #check
  (siteMorphismOfTopoi_comp_morphismOfTopoi_id.{u, u + 1} X :
    (MorphismOfTopoiIn.comp (siteMorphismOfTopoi.{u, u + 1} X)
        (morphismOfTopoi.{u, u + 1} (𝟙 X))).inverseImage ≅
      (MorphismOfTopoiIn.id (spacesEtaleTopology X)).inverseImage)

/- Lemma 73.4.8 (4): the inverse image `i_X⁻¹` equals the direct image
`π_{X,*}`. -/
@[stacks 0DF3] #check
  (morphismOfTopoi_id_inverseImage_eq_siteMorphismOfTopoi_pushforward.{u, u + 1} X :
    (morphismOfTopoi.{u, u + 1} (𝟙 X))⁻¹ =
      (siteMorphismOfTopoi.{u, u + 1} X).pushforward)

/- Lemma 73.4.8 (5): the direct image `π_{X,*}` evaluates a big-étale sheaf
on the relocalized spaces-étale object. -/
@[stacks 0DF3] #check
  (siteMorphismOfTopoi_pushforward_obj_obj.{u, u + 1} X :
    ∀ (𝒢 : Sheaf (overEtaleTopology X) (Type (u + 1))) (U : spacesEtaleSite X),
      ((siteMorphismOfTopoi.{u, u + 1} X).pushforward.obj 𝒢).1.obj (op U) =
        𝒢.1.obj (op ((relocalizationFunctor (𝟙 X)).obj U)))

end AlgebraicGeometry.AlgebraicSpace
