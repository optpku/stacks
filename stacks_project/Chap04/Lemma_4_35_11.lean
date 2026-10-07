module

public import ReasLib.CategoryTheory.Bicategory.Equivalence.Calculus.Whiskering
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

open scoped Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]
variable {a b c d : B} (e₁ : a ≌ b) (e₂ : c ≌ d)

/- Lemma 4.35.11: precomposition and postcomposition by equivalences over the base induce an
equivalence of hom-categories. This is the generic bicategorical whiskering theorem, not a
fibered-category-specific wrapper. -/
@[stacks 03YT]
#check (Bicategory.prePostcomp_isEquivalence e₁ e₂ :
  Functor.IsEquivalence
    (Bicategory.postcomp b e₂.hom ⋙ Bicategory.precomp d e₁.hom))

end CategoryTheory
