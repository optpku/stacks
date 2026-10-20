module

public import ReasLib.Algebra.Module.Graded.Quotient
public import ReasLib.Algebra.Module.Graded.Quotient.RestrictScalars
import StacksCheckRecall

@[expose] public section

/-!
# Homogeneous quotient pieces

This support file is a canonical recall surface for quotient component infrastructure.  It does not
restate the Proposition 10.58.7 proof's short-exact scaffolding.
-/

/- API design: the reusable quotient owners use `ℳ : ι → Submodule R M`; the former chapter file
used `Submodule S M` and rebuilt degree-zero restriction instances at every declaration.  Those
helpers are removed rather than retained under a weaker or misleading statement. -/

@[stacks 00K1 "homogeneous quotient component infrastructure"]
#check @DirectSum.Decomposition.quotientComponentMap
#check @DirectSum.Decomposition.quotientPredecompose
#check @DirectSum.Decomposition.quotientDecompose
#check @DirectSum.Decomposition.quotientDecomposition
#check @DirectSum.Decomposition.quotientRestrictScalars
#check @Submodule.mapGradedSMul
