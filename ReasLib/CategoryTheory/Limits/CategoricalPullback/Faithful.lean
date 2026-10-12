/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import ReasLib.CategoryTheory.Discrete.Equivalence

/-!
# Faithfulness and thinness for categorical pullbacks

The projection from a categorical pullback reflects morphisms whenever the opposite cospan leg
is faithful.  Thinness of one source can therefore be transported to the pullback.  These facts
belong to the explicit categorical-pullback model and do not depend on fibered categories.
-/

@[expose] public section

universe uA vA uB vB uT vT

namespace CategoryTheory.Limits.CategoricalPullback

variable {A : Type uA} {B : Type uB} {T : Type uT}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vT} T]

/-- The right projection from a categorical pullback is faithful when the left cospan leg is
faithful. -/
instance pi₂_faithful (L : A ⥤ T) (R : B ⥤ T) [L.Faithful] :
    (π₂ L R).Faithful := sorry

/-- The left projection from a categorical pullback is faithful when the right cospan leg is
faithful. -/
instance pi₁_faithful (L : A ⥤ T) (R : B ⥤ T) [R.Faithful] :
    (π₁ L R).Faithful := sorry

/-- A categorical pullback is thin when its left cospan leg is faithful and its right source is
thin. -/
instance isThin_of_left (L : A ⥤ T) (R : B ⥤ T)
    [L.Faithful] [Quiver.IsThin B] :
    Quiver.IsThin (CategoricalPullback L R) := sorry

/-- A categorical pullback is thin when its right cospan leg is faithful and its left source is
thin. -/
instance isThin_of_right (L : A ⥤ T) (R : B ⥤ T)
    [R.Faithful] [Quiver.IsThin A] :
    Quiver.IsThin (CategoricalPullback L R) := sorry

end CategoryTheory.Limits.CategoricalPullback
