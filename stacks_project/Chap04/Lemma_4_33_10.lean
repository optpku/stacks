/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Fibered.Pith
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped Bicategory

universe u v w vB

namespace CategoryTheory.LocallyInduced.TwoFibreProduct.Pith

variable {C : Type u} [Category.{v} C]
variable {X Y S : Bicategory.Pith
  (FiberedCategoryOver.{u, v, max w (max u (max v vB)), max v vB} C)}
variable (F : X ⟶ S) (G : Y ⟶ S)

/- Lemma 4.33.10: the `(2,1)`-category of fibred categories over a fixed base has two-fibre
products, represented by the explicit based pseudo-pullback cone. -/
@[stacks 02XQ]
#check (cone.isBiterminal F G : Bicategory.IsBiterminal (cone F G))

end CategoryTheory.LocallyInduced.TwoFibreProduct.Pith
