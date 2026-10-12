/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Basis.Presentation
import StacksCheckRecall

@[expose] public section

/- Lemma 18.30.10: finite basis cokernel presentations are closed under extensions. -/
@[stacks 093G]
#check @SheafOfModules.Localization.Basis.finitePresentationClosedUnderExtensions

/- Sieve-saturated specialization. -/
#check @SheafOfModules.Localization.Basis.finitePresentation_isClosedUnderExtensions
