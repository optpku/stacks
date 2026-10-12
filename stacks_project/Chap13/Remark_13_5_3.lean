/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.MorphismProperty.Triangulated.Basic
import StacksCheckRecall.CommandCrossRef

@[expose] public section

/- Remark 13.5.3 (Stacks 0H30): the one-shift and triangle-completion
presentation of triangulation compatibility is owned by the neutral
`MorphismProperty.Triangulated` API. -/

@[stacks 0H30]
#check @CategoryTheory.MorphismProperty.Triangulated.isomorphisms_le

@[stacks 0H30]
#check @CategoryTheory.MorphismProperty.Triangulated.of_one

@[stacks 0H30]
#check @CategoryTheory.MorphismProperty.Triangulated.one_iff_compatibleShift

@[stacks 0H30]
#check @CategoryTheory.MorphismProperty.Triangulated.one_iff_all
