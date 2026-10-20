module

import StacksCheckRecall
public import stacks_project.Chap66.Lemma_66_22_3_Instances
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StructureSheaf.LocallyRinged

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.22.3: for a scheme `S` and an algebraic space `X` over `S`, the small étale
site `X_étale` endowed with its structure sheaf `𝒪_X` (`commStructureSheafLift X`) is a
locally ringed site in the sense of `Sheaf.IsLocallyRinged` (Definition 18.40.4). -/
@[stacks 04KH] #check
  (AlgebraicGeometry.AlgebraicSpace.commStructureSheafLift_isLocallyRinged :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
      (AlgebraicGeometry.AlgebraicSpace.commStructureSheafLift X).IsLocallyRinged)

end AlgebraicGeometry.AlgebraicSpace
