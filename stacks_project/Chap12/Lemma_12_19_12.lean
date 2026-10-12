/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Strict.Abelian
import StacksCheckRecall

/-!
# Lemma 12.19.12

Source-facing checks for the three canonical short exact sequences on graded pieces.  Their
filtered data and exactness statements are owned by the abelian strict-morphism leaf in ReasLib.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (A : FilteredObject C) (X : Subobject A.obj)

/- Lemma 12.19.12 (1) [05SP]: the induced filtration on a subobject and the quotient filtration
give a short exact sequence on each graded piece. -/
@[stacks 05SP]
#check (FilteredObject.Subobject.Graded.shortExact A X :
  ∀ p : ℤ, (FilteredObject.Subobject.Graded.shortComplex A X p).ShortExact)

namespace FilteredObject.Hom

variable {A B : FilteredObject C} (f : A ⟶ B)

/- Lemma 12.19.12 (2) [05SP]: the filtered kernel and coimage give a short exact sequence on each
graded piece. -/
@[stacks 05SP]
#check (Graded.Coimage.shortExact f :
  ∀ p : ℤ, (Graded.Coimage.shortComplex f p).ShortExact)

/- Lemma 12.19.12 (3) [05SP]: the filtered image and cokernel give a short exact sequence on each
graded piece. -/
@[stacks 05SP]
#check (Graded.Image.shortExact f :
  ∀ p : ℤ, (Graded.Image.shortComplex f p).ShortExact)

end FilteredObject.Hom
end CategoryTheory
