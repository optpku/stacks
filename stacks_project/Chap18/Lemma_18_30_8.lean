/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Basis.Presentation
import StacksCheckRecall

@[expose] public section

/- Lemma 18.30.8: finite basis cokernel presentations are closed under cokernels. -/
@[stacks 093E]
#check @SheafOfModules.Localization.Basis.finitePresentationClosedUnderCokernels

/- Sieve-saturated specialization. -/
#check @SheafOfModules.Localization.Basis.finitePresentation_isClosedUnderCokernels
