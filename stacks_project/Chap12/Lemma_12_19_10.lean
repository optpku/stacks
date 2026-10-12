/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Strict.Pushout
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory.FilteredObject.Hom

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A B D : FilteredObject C} (f : A ⟶ B) (g : A ⟶ D)

/- Lemma 12.19.10 [05SM]: the standard filtered pushout exists. -/
@[stacks 05SM]
#check (inferInstance : HasPushout f g)

/- Lemma 12.19.10 [05SM]: its canonical right leg preserves strictness. -/
@[stacks 05SM]
#check (strict_pushout_inr_of_strict f g : Strict f → Strict (pushout.inr f g))

end CategoryTheory.FilteredObject.Hom
