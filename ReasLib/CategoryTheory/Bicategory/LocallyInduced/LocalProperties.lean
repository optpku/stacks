/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Construction
public import Mathlib.CategoryTheory.Groupoid

/-!
# Local properties of locally induced bicategories

This leaf owns properties inherited separately by each selected hom-category.
The pointwise hypotheses are intentionally weaker than requiring the entire
ambient bicategory to be locally groupoidal.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

universe w v u u'

namespace Bicategory.LocallyInducedBicategory

variable {B : Type u'} {C : Type u} [Bicategory.{w, v} C]
variable {F : B → C} {Q : HomProperty F} [Q.IsMultiplicative]

/-- Each hom-category of a locally induced bicategory inherits groupoidality
from its corresponding ambient hom-category. -/
@[stacks 0040 "groupoidal homs of a locally induced bicategory"]
instance homGroupoid
    (X Y : LocallyInducedBicategory C F Q) [IsGroupoid (F X ⟶ F Y)] :
    IsGroupoid (X ⟶ Y) := sorry
/- Proof strategy: identify `X ⟶ Y` with `(Q X Y).FullSubcategory`; lift the
ambient inverse of each `2`-morphism through `ObjectProperty.homMk`, and prove
both inverse laws with `ObjectProperty.hom_ext`. -/

end Bicategory.LocallyInducedBicategory

end CategoryTheory
