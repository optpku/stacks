/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Separated.AffineCriterion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.21.7 (1): affine opens over a common affine target have affine intersection under a
separated morphism. -/
@[stacks 01KP] #check Scheme.Hom.isAffineOpen_inter_of_isSeparated

/- Lemma 26.21.7 (2): the absolute section-tensor comparison is surjective. -/
@[stacks 01KP] #check
  Scheme.Hom.sectionTensorToIntersection_surjective_of_isSeparated

/- The relative pushout comparison is the canonical algebraic owner behind the criterion. -/
#check Scheme.Hom.HasCommonAffineTarget
#check Scheme.Hom.CommonAffineTarget
#check Scheme.Hom.hasCommonAffineTarget_iff_nonempty
#check Scheme.Hom.hasCommonAffineTarget_comm
#check Scheme.Hom.CommonAffineTarget.swap
#check Scheme.Hom.CommonAffineTarget.sectionsComparison
#check Scheme.Hom.CommonAffineTarget.sectionsComparison_surjective_iff
#check Scheme.Hom.CommonAffineTarget.sectionsComparison_surjective
#check Scheme.Hom.sectionPushoutToIntersection
#check Scheme.Hom.sectionPushoutToIntersection_surjective_iff
#check Scheme.Hom.sectionPushoutToIntersection_surjective_of_isSeparated

/- Lemma 26.21.7 (3): the source-facing affine-neighborhood conditions characterize
separatedness. -/
@[stacks 01KP] #check Scheme.Hom.isSeparated_of_exists_affineNeighborhoods

@[stacks 01KP] #check Scheme.Hom.isSeparated_iff_exists_affineNeighborhoods
#check Scheme.Hom.isSeparated_iff_exists_affineNeighborhoods_of_sectionPushout

#check Scheme.Hom.isSeparated_of_exists_affineNeighborhoods_of_sectionPushout
