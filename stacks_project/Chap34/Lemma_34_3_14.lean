module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.Small

@[expose] public section

open CategoryTheory
open Opposite
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

/-- The identity-base small-to-big Zariski site morphism, traditionally denoted `π_S`. -/
abbrev smallZariskiToBigZariskiSiteMorphismOfTopoi :
    MorphismOfTopoiIn S.smallZariskiTopology S.bigZariskiTopology :=
  Zariski.SmallToBig.siteMorphismOfTopoi S

/- Lemma 34.3.14 (1): the identity-base relocalization functor defines a morphism
of small-to-big Zariski sites. -/
@[stacks 020Z] #check
  (AlgebraicGeometry.Scheme.Zariski.SmallToBig.identity_isMorphismOfSites S :
    CategoryTheory.IsMorphismOfSites S.smallZariskiTopology S.bigZariskiTopology
      (AlgebraicGeometry.Scheme.Zariski.SmallToBig.relocalizationFunctor (𝟙 S)))

/- Lemma 34.3.14 (2): the identity-base site morphism induces the morphism of
topoi `π_S`. -/
@[stacks 020Z] #check
  (AlgebraicGeometry.Scheme.Zariski.SmallToBig.siteMorphismOfTopoi S :
    MorphismOfTopoiIn S.smallZariskiTopology S.bigZariskiTopology)

/- Lemma 34.3.14 (3): the site-induced morphism `π_S` composed with
`i_S = i_{𝟙 S}` is the identity on the small Zariski topos. -/
@[stacks 020Z] #check
  (AlgebraicGeometry.Scheme.Zariski.SmallToBig.siteMorphismOfTopoi_comp_morphismOfTopoi_id S :
    MorphismOfTopoiIn.comp
        (AlgebraicGeometry.Scheme.Zariski.SmallToBig.siteMorphismOfTopoi S)
        (AlgebraicGeometry.Scheme.Zariski.SmallToBig.morphismOfTopoi (𝟙 S)) =
      MorphismOfTopoiIn.id S.smallZariskiTopology)

/- Lemma 34.3.14 (4): the direct image `π_{S,*}` evaluates a big-Zariski sheaf
on the relocalized small-Zariski object. -/
@[stacks 020Z] #check
  (AlgebraicGeometry.Scheme.Zariski.SmallToBig.siteMorphismOfTopoi_pushforward_obj_obj S :
    ∀ (𝒢 : Sheaf S.bigZariskiTopology (Type (u + 1))) (U : S.smallZariskiSite),
      ((AlgebraicGeometry.Scheme.Zariski.SmallToBig.siteMorphismOfTopoi S).pushforward.obj 𝒢).1.obj
          (op U) =
        𝒢.1.obj (op
          ((AlgebraicGeometry.Scheme.Zariski.SmallToBig.relocalizationFunctor (𝟙 S)).obj U)))

end AlgebraicGeometry.Scheme
