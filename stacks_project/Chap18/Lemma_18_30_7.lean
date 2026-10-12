/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization.Basis.Presentation
import StacksCheckRecall

@[expose] public section

/- Equation 18.30.7.1: finite coequalizer presentations by basis sheafified representables. -/
@[stacks 09Y7]
#check @CategoryTheory.GrothendieckTopology.Basis.finiteSheafPresentation

/- Equation 18.30.7.2: finite cokernel presentations by basis structure modules. -/
@[stacks 093D]
#check @SheafOfModules.Localization.Basis.finitePresentation

/- Lemma 18.30.7 (1): every set-valued sheaf is generated under filtered colimits by finite
basis coequalizer presentations. -/
@[stacks 093C "(1)"]
#check @CategoryTheory.Coverage.Basis.finiteSheafPresentationInd

/- Lemma 18.30.7 (2): every module sheaf is generated under filtered colimits by finite basis
cokernel presentations. -/
@[stacks 093C "(2)"]
#check @SheafOfModules.Localization.Basis.finitePresentationInd

/- Sieve-saturated specializations remain available for Grothendieck-topology inputs. -/
#check @CategoryTheory.GrothendieckTopology.Basis.finiteSheafPresentation_ind
#check @SheafOfModules.Localization.Basis.finitePresentation_ind
