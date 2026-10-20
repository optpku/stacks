module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealQuotient.ClosedImmersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Example 26.4.3: a locally surjective quotient of `𝒪_X` is carried by its closed support;
its canonical inclusion is a closed immersion when the kernel is locally generated. -/
@[stacks 01HM "closed quotient support"]
#check LocallyRingedSpace.SupportedQuotient.isClosed_support
#check LocallyRingedSpace.SupportedQuotient.space
#check LocallyRingedSpace.SupportedQuotient.ι
#check LocallyRingedSpace.SupportedQuotient.ι_isClosedImmersion
#check LocallyRingedSpace.SupportedQuotient.ι_isAssociated
#check LocallyRingedSpace.SupportedQuotient.pushforwardComparison
#check LocallyRingedSpace.SupportedQuotient.pushforwardComparison_isIso

/- An ideal quotient is the canonical specialization obtained from a locally generated ideal
subobject. -/
@[stacks 01HM] #check LocallyRingedSpace.IdealQuotient.isClosedImmersion_ι
#check LocallyRingedSpace.IdealQuotient.sheaf
#check LocallyRingedSpace.IdealQuotient.projection
#check LocallyRingedSpace.IdealQuotient.space
#check LocallyRingedSpace.IdealQuotient.ι
#check LocallyRingedSpace.IdealQuotient.range_ι_base
#check LocallyRingedSpace.IdealQuotient.ι_isAssociated
