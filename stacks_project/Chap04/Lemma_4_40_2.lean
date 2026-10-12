/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Representable.Setoids
public import ReasLib.CategoryTheory.Fibered.Representable.Presentation
import StacksCheckRecall

@[expose] public section

universe u v

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable (P : FiberedCategoryOver.Groupoids C)
variable {X X' : C}
variable (j : P ≌ FiberedCategoryOver.Groupoids.slice X)
variable (j' : P ≌ FiberedCategoryOver.Groupoids.slice X')

/- Lemma 4.40.2 (1): a category fibred in groupoids is representable if and only if it is
fibred in setoids and its presheaf of fiberwise isomorphism classes is representable. -/
@[stacks 02Y3 "(1)"]
#check (FiberedCategoryOver.Groupoids.IsRepresentable.iff_inSetoids_and_fiberClasses P :
  P.IsRepresentable ↔
    Functor.IsFibered.InSetoids P.p ∧
      (Functor.fiberIsoClassPresheaf P.p).IsRepresentable)

/- Lemma 4.40.2 (2): two presentations by slice projections have isomorphic representing
objects, compatibly with the presentations up to a `2`-isomorphism. -/
@[stacks 02Y3 "(2)"]
#check (FiberedCategoryOver.Groupoids.Presentation.uniqueUpToIso j j' :
  ∃ i : X ≅ X',
    Nonempty
      (j'.hom ≅ j.hom ≫ FiberedCategoryOver.Groupoids.overMap i.hom))

end CategoryTheory
