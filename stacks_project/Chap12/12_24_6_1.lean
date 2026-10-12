/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Morphism.PageRepresentatives
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Equation 12.24.6.1 [012S] is the specialization to a filtered-complex differential of the
morphism-level inclusion of intrinsic cycles into the eventual cycle representative. -/
@[stacks 012S]
#check FilteredObject.Hom.Representative.Cycle.kernel_le_eventual
