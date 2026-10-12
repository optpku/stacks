/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Final
import StacksCheckRecall

@[expose] public section

universe vI uI vJ uJ

namespace CategoryTheory.Functor

variable {I : Type uI} [Category.{vI} I]
variable {J : Type uJ} [Category.{vJ} J]
variable (H : I ⥤ J)

/- The source's pairs `(x, H.obj x ⟶ y)` and their commuting zigzags are exactly the objects and
morphisms of `CostructuredArrow H y`. The verified `Functor.Initial` owner requires these categories
to be `IsConnected`, which supplies both nonemptiness and arbitrary finite zigzag connectivity;
`IsConnected` alone is only the objectwise ingredient, while a separate iff bridge would duplicate
this definition. Thus the recall introduces no generalization and exposes the standard initial-functor
API for later limit arguments. -/

/- Definition 4.17.3: a functor `H : I ⥤ J` is initial when every category
`CostructuredArrow H y` is connected. -/
@[stacks 09WP "initial functors via connected costructured-arrow categories"]
#check (Initial H : Prop)

end CategoryTheory.Functor
