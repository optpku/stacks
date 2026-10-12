/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Yoneda
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Lemma 59.9.3 (Yoneda) -/
@[stacks 03NE] #check (CategoryTheory.Yoneda.map_bijective (C := C) :
  ∀ X Y : C, Function.Bijective (yoneda.map : (X ⟶ Y) → (yoneda.obj X ⟶ yoneda.obj Y)))

end CategoryTheory
