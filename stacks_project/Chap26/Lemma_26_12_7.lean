/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Factorization
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.Coreflection
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.Over.Coreflection
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry.Scheme

/- Lemma 26.12.7 (1): a map from a reduced scheme factors through a closed subscheme exactly
when its range lies in the closed support. -/
@[stacks 0356] #check IsClosedImmersion.exists_lift_iff_range_subset
#check IsClosedImmersion.existsUnique_lift_iff_range_subset
#check IsClosedImmersion.ker_le_ker_iff_range_subset
#check IdealSheafData.exists_lift_iff_range_subset
#check IdealSheafData.existsUnique_lift_iff_range_subset
#check IdealSheafData.lift
#check IdealSheafData.lift_subschemeι

/- Lemma 26.12.7 (2): every map from a reduced scheme canonically factors through the target
reduction. -/
@[stacks 0356] #check Hom.reductionLift
#check Hom.reductionι_ker_le_ker_of_isReduced
#check Hom.reductionLift_reductionι
#check Hom.reductionHomEquiv
#check Reduced.coreflector
#check Reduced.adjunction
#check Reduced.adjunction_counit_app

/- Relative companion: reductions over a fixed base have the parallel coreflection API. -/
#check _root_.AlgebraicGeometry.Over.Reduced.coreflector
#check _root_.AlgebraicGeometry.Over.Reduced.adjunction
#check _root_.AlgebraicGeometry.Over.Reduced.adjunction_counit_app

end AlgebraicGeometry.Scheme
