module

import ReasLib.AlgebraicGeometry.ProjectiveSpace.ComplexConic.ProjectiveLine
import StacksCheckRecall

@[expose] public section

/- Exercise 111.37.3: an explicit scheme isomorphism
`ProjectiveLine.scheme ℂ ≅ ComplexConic.scheme`, recovering the source arrow
`ProjectiveLine.scheme ℂ ⟶ Proj (ℂ[X_0, X_1, X_2] / (X_0 ^ 2 + X_1 ^ 2 + X_2 ^ 2))`. -/
@[stacks 029Z] #check (AlgebraicGeometry.ComplexConic.projectiveLineIso :
  AlgebraicGeometry.ProjectiveLine.scheme ℂ ≅ AlgebraicGeometry.ComplexConic.scheme)
