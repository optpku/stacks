module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent
import StacksCheckRecall

@[expose] public section

open SheafOfModules.RingedSite

/- Definition 18.35.1: the naive cotangent complex of a morphism of ring sheaves is the
two-term complex of the canonical polynomial presentation, with the conormal map as differential.
The site-generic construction is owned by ReasLib. -/
@[stacks 08TW]
#check @NaiveCotangent.obj

#check @NaiveCotangent.Presentation.complex
#check @NaiveCotangent.Presentation.X_negOne
#check @NaiveCotangent.Presentation.X_zero
#check @NaiveCotangent.Presentation.d_negOne_zero
#check @NaiveCotangent.X_negOne
#check @NaiveCotangent.X_zero
#check @NaiveCotangent.d_negOne_zero
