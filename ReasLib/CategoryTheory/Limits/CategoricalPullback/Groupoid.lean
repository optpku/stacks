module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

/-!
# Groupoid categorical pullbacks

The explicit categorical pullback of groupoids is again a groupoid. This is a fact about the
categorical-pullback model itself, independent of any fibration over a base.
-/

@[expose] public section

universe uA vA uB vB uT vT

namespace CategoryTheory

namespace Limits.CategoricalPullback

/-- A categorical pullback of groupoids is again a groupoid. -/
instance isGroupoid
    {A : Type uA} [Category.{vA} A]
    {B : Type uB} [Category.{vB} B]
    {T : Type uT} [Category.{vT} T]
    (L : A ⥤ T) (R : B ⥤ T) [IsGroupoid A] [IsGroupoid B] :
    IsGroupoid (Limits.CategoricalPullback L R) := sorry
/- Proof strategy: use `Limits.CategoricalPullback.isIso_iff`; both components of every
pullback morphism are isomorphisms because the two source categories are groupoids. -/

end Limits.CategoricalPullback

end CategoryTheory
