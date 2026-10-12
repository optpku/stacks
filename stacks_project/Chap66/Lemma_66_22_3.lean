/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_22_3_Instances

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 66.22.3: for a scheme `S` and an algebraic space `X` over `S`, the small étale
site `X_étale` endowed with its structure sheaf `𝒪_X` (`commStructureSheafLift X`) is a
locally ringed site in the sense of `Sheaf.IsLocallyRinged` (Definition 18.40.4). -/
@[stacks 04KH, instance]
instance commStructureSheafLift_isLocallyRinged' {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (commStructureSheafLift X).IsLocallyRinged :=
  inferInstance

end AlgebraicGeometry.AlgebraicSpace
