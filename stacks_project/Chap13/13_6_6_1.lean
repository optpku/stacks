/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.ObjectProperty.Localization.Triangulated.Saturation
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.ObjectProperty

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (P : ObjectProperty D)

/- 13.6.6.1: the source's arrows occurring in a distinguished triangle with third object in the
strictly full subcategory are precisely the canonical cone-defined property
`P.isoClosure.trW`. -/
@[stacks 05RH] #check
  P.isoClosure.trW_iff

/- Passing to isomorphism closure does not change the cone-defined morphism property. -/
#check P.trW_isoClosure

end CategoryTheory.ObjectProperty
