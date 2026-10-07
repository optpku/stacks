module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry

/- Lemma 26.12.4: every closed subset carries a unique reduced closed-subscheme structure. -/
@[stacks 01J3] #check Scheme.ClosedSubschemeStructure.existsUnique_reduced
#check Scheme.ClosedSubschemeStructure.isReduced_iff_eq_reduced
#check Scheme.IdealSheafData.support_vanishingIdeal
#check Scheme.IdealSheafData.subscheme_isReduced_iff_radical_eq
#check Scheme.IdealSheafData.radical_vanishingIdeal
#check Scheme.IdealSheafData.vanishingIdeal_subscheme_isReduced
#check Scheme.IdealSheafData.eq_vanishingIdeal
#check Scheme.IdealSheafData.support_eq_and_isReduced_iff

end AlgebraicGeometry
