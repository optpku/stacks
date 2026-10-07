module

public import ReasLib.AlgebraicGeometry.Scheme.Gluing.DoubleAlong.AffineSpace
import StacksCheckRecall

@[expose] public section

/- Remark 26.11.3: two affine opens can have non-affine intersection. -/
@[stacks 01IU] #check
  AlgebraicGeometry.DoubledOrigin.chart_inf_not_isAffineOpen
#check AlgebraicGeometry.DoubledOrigin.chart_isAffineOpen
