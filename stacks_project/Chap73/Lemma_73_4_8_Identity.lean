module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.IdentityRelocalization
public import stacks_project.Chap66.Lemma_66_18_8_Pullback
public import stacks_project.Chap73.Lemma_73_4_7_Relocalization

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped MorphismOfTopoiIn

universe u

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/- Lemma 73.4.8: the identity-base inclusion induces a morphism of topoi from
the big étale slice topos to the spaces-étale topos. -/
@[stacks 0DF3] #check (AlgebraicGeometry.AlgebraicSpace.Etale.SpacesToBig.siteMorphismOfTopoi.{u, u + 1} X :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, u + 1}
      (AlgebraicSpace.spacesEtaleTopology X) (AlgebraicSpace.overEtaleTopology X))
