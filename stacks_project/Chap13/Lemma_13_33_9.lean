/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Homological
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.33.9

The source specialization is an instance of the generic image-comparison API
for a distinguished telescope triangle and the represented Hom functor.  The
selected-coproduct layer adds theorem interfaces but no second comparison-map
definition.
-/

#check @CategoryTheory.HomotopyColimit.Presentation.imageComparison
#check @CategoryTheory.HomotopyColimit.Presentation.imageComparison_isIso
#check @CategoryTheory.HomotopyColimit.SelectedCoproduct.colimit_ι_comp_imageComparison

@[stacks 094A]
#check @CategoryTheory.HomotopyColimit.SelectedCoproduct.PreadditiveCoyoneda.imageComparison_isIso
