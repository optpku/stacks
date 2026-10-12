/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.Localization.Preadditive
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory

open MorphismProperty

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
  [W.HasRightCalculusOfFractions] (X : C)

/- Lemma 12.8.3: a localized object is zero iff an outgoing zero morphism is inverted, iff an
incoming zero morphism is inverted. -/
@[stacks 05QF]
#check MorphismProperty.Localization.objectIsZero_tfae W X

/- The two directions are also exposed independently for direct downstream rewriting. -/
#check MorphismProperty.Localization.objectIsZero_iff_exists_zero_out W X
#check MorphismProperty.Localization.objectIsZero_iff_exists_zero_in W X

end CategoryTheory
