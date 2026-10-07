module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Small

@[expose] public section

open CategoryTheory
open Opposite
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

/-- The identity-base small-to-big étale site morphism, traditionally denoted `π_S`. -/
abbrev smallEtaleToBigEtaleSiteMorphismOfTopoi :
    MorphismOfTopoiIn S.smallEtaleTopology (S.overGrothendieckTopology @Etale) :=
  Etale.SmallToBig.siteMorphismOfTopoi S

/- Lemma 34.4.14 (1): the identity-base relocalization functor defines a morphism
of small-to-big étale sites. -/
@[stacks 021G] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.identity_isMorphismOfSites S :
    CategoryTheory.IsMorphismOfSites S.smallEtaleTopology
      (S.overGrothendieckTopology @Etale)
      (AlgebraicGeometry.Scheme.Etale.SmallToBig.relocalizationFunctor (𝟙 S)))

/- Lemma 34.4.14 (2): the identity-base site morphism induces the morphism of
topoi `π_S`. -/
@[stacks 021G] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.siteMorphismOfTopoi S :
    MorphismOfTopoiIn S.smallEtaleTopology (S.overGrothendieckTopology @Etale))

/- Lemma 34.4.14 (3): the site-induced morphism `π_S` composed with
`i_S = i_{𝟙 S}` is the identity on the small étale topos. -/
@[stacks 021G] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.siteMorphismOfTopoi_comp_morphismOfTopoi_id S :
    MorphismOfTopoiIn.comp
        (AlgebraicGeometry.Scheme.Etale.SmallToBig.siteMorphismOfTopoi S)
        (AlgebraicGeometry.Scheme.Etale.SmallToBig.morphismOfTopoi (𝟙 S)) =
      MorphismOfTopoiIn.id S.smallEtaleTopology)

/- Lemma 34.4.14 (4): the inverse image `i_S⁻¹` equals the direct image
`π_{S,*}`. -/
@[stacks 021G] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.morphismOfTopoi_id_inverseImage_eq_siteMorphismOfTopoi_pushforward S :
    (AlgebraicGeometry.Scheme.Etale.SmallToBig.morphismOfTopoi (𝟙 S))⁻¹ =
      (AlgebraicGeometry.Scheme.Etale.SmallToBig.siteMorphismOfTopoi S).pushforward)

/- Lemma 34.4.14 (5): the direct image `π_{S,*}` evaluates a big-étale sheaf
on the relocalized small-étale object. -/
@[stacks 021G] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.siteMorphismOfTopoi_pushforward_obj_obj S :
    ∀ (𝒞 : Sheaf (S.overGrothendieckTopology @Etale) (Type (u + 1))) (U : S.Etale),
      ((AlgebraicGeometry.Scheme.Etale.SmallToBig.siteMorphismOfTopoi S).pushforward.obj 𝒞).1.obj
          (op U) =
        𝒞.1.obj (op
          ((AlgebraicGeometry.Scheme.Etale.SmallToBig.relocalizationFunctor (𝟙 S)).obj U)))

end AlgebraicGeometry.Scheme
