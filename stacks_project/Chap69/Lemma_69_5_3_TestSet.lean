module

public import ReasLib.CategoryTheory.Sites.QuasiCompact.TestSet
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Lemma_66_18_6_Site
public import stacks_project.Chap66.Lemma_66_18_8_Topos

/-!
# Quasi-compact test sets on the small étale site

On a quasi-compact and quasi-separated algebraic space, the affine objects of `X_étale`
form a refining basis, so the small étale topology admits a quasi-compact test set.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.GrothendieckTopology.QuasiCompact
open CategoryTheory.GrothendieckTopology.QuasiCompact.TestSet

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- On a quasi-compact and quasi-separated algebraic space, the affine objects of the small
étale site form a refining basis in the sense of Remark 7.17.9 (2). -/
instance affineEtaleObjects.instRefiningBasis {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    RefiningBasis (smallEtaleTopology X) (affineEtaleObjects X) :=
  sorry

/-- A quasi-compact and quasi-separated algebraic space has a quasi-compact test set on its
small étale topology. -/
instance smallEtaleTopology.instHasTestSet {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    HasTestSet (smallEtaleTopology X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
