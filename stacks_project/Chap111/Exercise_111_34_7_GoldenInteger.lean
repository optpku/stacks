module

public import ReasLib.AlgebraicGeometry.Scheme.GoldenInteger
import StacksCheckRecall

@[expose] public section

/- Exercise 111.34.7: the golden-integer scheme is a closed subscheme of the
localized affine line over the integers. -/
@[stacks 0299] #check
  (AlgebraicGeometry.GoldenIntegerQuasiSection.instIsClosedImmersion :
    AlgebraicGeometry.IsClosedImmersion
      AlgebraicGeometry.GoldenIntegerQuasiSection.closedImmersion)
