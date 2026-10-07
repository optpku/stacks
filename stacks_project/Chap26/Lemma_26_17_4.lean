module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Pullback.OpenCover

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.17.4: affine covers of the base and factors induce an affine
open cover of their fibre product. -/
@[stacks 01JS] #check Scheme.Pullback.affineOpenCover
#check Scheme.Pullback.affineOpenCover_opensRange
#check Scheme.Pullback.openCover
#check Scheme.Pullback.openCover_isAffine
