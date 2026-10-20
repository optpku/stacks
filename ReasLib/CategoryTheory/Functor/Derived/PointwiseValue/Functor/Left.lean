module

public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Left
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Functor of Pointwise Left-Derived Values

When pointwise left-derived values exist everywhere, their canonical maps assemble into a
functor independently of a chosen total derived functor.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.LeftDerived.Value

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

/-- Pointwise left-derived values and their canonical maps, assembled into a functor when they
exist at every source object. -/
@[stacks 05SA]
noncomputable def functor (F : C ⥤ D) (S : MorphismProperty C)
    [F.HasPointwiseLeftDerivedFunctor S] : C ⥤ D where
  obj X := obj F S X
  map f := map F S f
  map_id X := map_id F S X
  map_comp f g := map_comp F S f g

namespace functor

/-- The pointwise left-derived value functor is computed by `LeftDerived.Value.obj` on objects. -/
@[simp, stacks 05SA "pointwise left-derived value functor computation"]
theorem obj (F : C ⥤ D) (S : MorphismProperty C)
    [F.HasPointwiseLeftDerivedFunctor S] (X : C) :
    (functor F S).obj X = LeftDerived.Value.obj F S X := sorry

/-- The pointwise left-derived value functor is computed by `LeftDerived.Value.map` on morphisms. -/
@[simp, stacks 05SA "pointwise left-derived value functor computation"]
theorem map (F : C ⥤ D) (S : MorphismProperty C)
    [F.HasPointwiseLeftDerivedFunctor S] {X Y : C} (f : X ⟶ Y) :
    (functor F S).map f = LeftDerived.Value.map F S f := sorry

end functor



end CategoryTheory.Functor.LeftDerived.Value
