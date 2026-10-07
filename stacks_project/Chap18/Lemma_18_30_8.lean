module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Basis.Presentation
import StacksCheckRecall

@[expose] public section

/- Lemma 18.30.8: finite basis cokernel presentations are closed under cokernels. -/
@[stacks 093E]
#check @SheafOfModules.Localization.Basis.finitePresentationClosedUnderCokernels

/- Sieve-saturated specialization. -/
#check @SheafOfModules.Localization.Basis.finitePresentation_isClosedUnderCokernels
