module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiCompact
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry

/- Lemma 26.19.2 (1): quasi-compactness can be tested on every affine open. -/
@[stacks 01K4] #check quasiCompact_iff_forall_isAffineOpen

/- Lemma 26.19.2 (2): it can equivalently be checked on an affine open cover. -/
@[stacks 01K4] #check Scheme.Hom.quasiCompact_iff_pullback_compactSpace
@[stacks 01K4] #check Scheme.Hom.quasiCompact_iff_exists_affineOpenCover

end AlgebraicGeometry
