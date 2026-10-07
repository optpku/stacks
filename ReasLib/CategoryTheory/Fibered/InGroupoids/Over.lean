module

public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Fibered.InGroupoids
import Mathlib.Tactic.CrossRefAttribute

/-!
# Slice categories of categories fibred in groupoids

For a category fibred in groupoids, slicing at an object is equivalent to slicing the base at
its image.  This is a property of the projection functor itself, independently of a topology or
of the bundled `FiberedCategoryOver` bicategory.

## Main declarations

* `CategoryTheory.Functor.IsFibered.InGroupoids.overPost.isEquivalence` — the slice equivalence
  induced by a groupoid-fibred projection.
-/

@[expose] public section

universe uC uS vC vS

namespace CategoryTheory

namespace Functor.IsFibered.InGroupoids

variable {C : Type uC} {S : Type uS}
variable [Category.{vC} C] [Category.{vS} S]

/-- Lemma 8.10.4 (tag 0CN0): if `p` is fibred in groupoids, postcomposition with `p` induces an
equivalence from the slice category `S/x` to the slice category `C/p(x)`. -/
@[stacks 0CN0]
theorem overPost.isEquivalence (p : S ⥤ C) [Functor.IsFibered.InGroupoids p] (x : S) :
    (Over.post p : Over x ⥤ Over (p.obj x)).IsEquivalence := sorry

end Functor.IsFibered.InGroupoids

end CategoryTheory
