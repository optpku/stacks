/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.Pro.Sequential.Distinguished.EssentiallyConstant
import StacksCheckRecall

@[expose] public section

/- Lemma 13.42.2: a sequential system of distinguished triangles with essentially constant
outer terms admits a stage map to a distinguished triangle of values; its middle term is
essentially constant. -/
@[stacks 0G3A] #check @CategoryTheory.Pro.Sequential.Distinguished.EssentiallyConstant.existsStageRepresentative

#check @CategoryTheory.Pro.Sequential.Distinguished.EssentiallyConstant.existsValueTriangle
#check @CategoryTheory.Pro.Sequential.Distinguished.EssentiallyConstant.middle
