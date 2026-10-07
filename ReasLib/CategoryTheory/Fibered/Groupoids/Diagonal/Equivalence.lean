module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Computations
public import ReasLib.CategoryTheory.Fibered.Groupoids.FiberwiseEquivalence
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Diagonal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalence criteria for groupoid-fibred diagonals

This leaf contains only the fibrewise and fully-faithful criteria for the canonical diagonal.  The
universal-lift data is owned by `Diagonal.Construction` and its projection formulas by
`Diagonal.Computations`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped Bicategory CategoricalPullback

universe u v w

namespace CategoryTheory

namespace FiberedCategoryOver.Groupoids

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.Groupoids.{u, v, max w (max u v), v} C}
variable (F : X ⟶ Y)

namespace Hom.diagonal

/- The criterion is stated against the canonical diagonal owner, not its implementation lift. -/

/-- The canonical diagonal is an equivalence over the base exactly when every induced fibre
diagonal is an equivalence.  The conclusion uses the fixed-morphism
`BasedFunctor.IsEquivalence` property, so downstream code can use the standard quasi-inverse and
bicategorical packaging API without an equality transport. -/
theorem isEquivalence_iff_fiberwise :
    BasedFunctor.IsEquivalence (toBasedFunctor (Hom.diagonal F)) ↔
      ∀ U : C, (Δₚ (fiberFunctor F U)).IsEquivalence := sorry

/-- The underlying functor of the canonical diagonal is an ordinary equivalence exactly when the
original morphism is fully faithful. -/
theorem fullyFaithful_iff_toFunctor_isEquivalence :
    Nonempty (toBasedFunctor F).FullyFaithful ↔
      (toFunctor (Hom.diagonal F)).IsEquivalence := sorry

/-- A morphism of categories fibred in groupoids is fully faithful exactly when its canonical
diagonal is an equivalence over the base. -/
@[stacks 04Z7 "fully faithful iff the canonical diagonal is an equivalence"]
theorem fullyFaithful_iff_isEquivalence :
    Nonempty (toBasedFunctor F).FullyFaithful ↔
      BasedFunctor.IsEquivalence (toBasedFunctor (Hom.diagonal F)) := sorry

end Hom.diagonal

end FiberedCategoryOver.Groupoids

end CategoryTheory
