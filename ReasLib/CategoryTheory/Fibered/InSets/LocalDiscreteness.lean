module

public import ReasLib.CategoryTheory.Fibered.InSets.Bicategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local discreteness of categories fibred in sets

The full subbicategory of discrete fibrations has discrete hom-categories.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Sets

/-- Every hom-category of categories fibred in sets over `C` is discrete.
Equivalently, every `2`-morphism is an identity and the full subbicategory is
locally discrete. -/
@[stacks 02Y2 "(1)"]
instance homIsDiscrete (X Y : FiberedCategoryOver.Sets C) :
    IsDiscrete (X ⟶ Y) := sorry
/- Proof strategy: every component of a based natural transformation is vertical in a discrete target
fiber. Its existence forces the two component objects to agree, and uniqueness forces the
component to be the identity; functor and natural-transformation extensionality finish. -/

end FiberedCategoryOver.Sets

end CategoryTheory
