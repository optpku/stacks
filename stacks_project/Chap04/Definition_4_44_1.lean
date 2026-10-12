/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Construction
import StacksCheckRecall

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

variable {B : Type u} [Bicategory.{w, v} B]
variable {T X Y : B} {y : T ⟶ Y} {p : X ⟶ Y}
variable (sq : Bicategory.PseudoPullbackCone y p)
variable (A A' : DottedArrow sq)

/- Definition 4.44.1 (1): a dotted arrow for a `2`-commutative square is represented by the
canonical general-purpose owner `DottedArrow`. -/
@[stacks 0H18 "dotted-arrow data and triangular coherence"]
#check (DottedArrow sq : Type (max w v))

/- Definition 4.44.1 (2): morphisms of dotted arrows are represented by the compatible ambient
`2`-morphisms in `DottedArrow.Hom`. -/
@[stacks 0H18 "morphisms of dotted arrows and comparison compatibility"]
#check (DottedArrow.Hom A A' : Type w)

end CategoryTheory
