/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.Faithful
import StacksCheckRecall

@[expose] public section

universe u v

namespace CategoryTheory

namespace FiberedCategoryOver.Groupoids

variable {C : Type u} [Category.{v} C]
variable {X Y : Groupoids C}
variable {F : X ⟶ Y}
variable (hF : relativelyRepresentable F) (U : C)

/- Lemma 4.42.4: a relatively representable morphism of categories fibred in groupoids is
faithful on every fiber. -/
@[stacks 02Y8]
#check (relativelyRepresentable.fiberwiseFaithful hF U :
  (fiberFunctor F U).Faithful)

/- The same narrow owner exposes the equivalent total-faithfulness consequence. -/
#check relativelyRepresentable.faithful

end FiberedCategoryOver.Groupoids

end CategoryTheory
