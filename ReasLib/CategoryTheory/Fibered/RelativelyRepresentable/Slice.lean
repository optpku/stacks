/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map

/-!
# Relative representability of canonical slice maps

Canonical slice maps are relatively representable when the base category has
pullbacks, and their slice base changes are representable.
-/

@[expose] public section

universe u v

namespace CategoryTheory.FiberedCategoryOver.Groupoids.relativelyRepresentable

open scoped Bicategory

/-- If the base category has fibre products, then the canonical morphism
`overMap f : slice X ⟶ slice Y` induced by `f : X ⟶ Y` is relatively representable. -/
theorem overMap {C : Type u} [Category.{v} C]
    [Limits.HasPullbacks C] {X Y : C} (f : X ⟶ Y) :
    relativelyRepresentable (overMap f) := sorry

/-- The slice base change of a relatively representable canonical slice morphism
along `G : slice U ⟶ slice Y` is representable. -/
theorem overMap.baseChange_isRepresentable
    {C : Type u} [Category.{v} C] [Limits.HasPullbacks C] {X Y : C} (f : X ⟶ Y)
    {U : C} (G : slice U ⟶ slice Y) :
    IsRepresentable (baseChange (FiberedCategoryOver.Groupoids.overMap f) G) := sorry

end CategoryTheory.FiberedCategoryOver.Groupoids.relativelyRepresentable
