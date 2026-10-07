module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiCompact
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry

/- Lemma 26.19.7: a quasi-compact scheme-morphism image is closed exactly when it is stable
under specialization. -/
@[stacks 05JL] #check Scheme.Hom.isClosed_range_iff_stableUnderSpecialization

end AlgebraicGeometry
