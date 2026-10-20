module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-!
# Categories fibred in groupoids

The intrinsic projection-level owner and its strongly-cartesian recognition API. Fiberwise
groupoid characterizations are separated into `InGroupoids.Fibers` so users of the owner do not
need to import the bundled groupoid layer.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.IsFibered

open CategoryTheory Functor IsStronglyCartesian

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]

/-- A functor `p : S ⥤ C` is fibred in groupoids if it is fibered and every morphism of `S` is
Cartesian over its image in `C`. -/
@[stacks 003T]
class InGroupoids (p : S ⥤ C) : Prop extends p.IsFibered where
  /-- Every total-category morphism is Cartesian over its image in the base. -/
  all_isCartesian {x y : S} (φ : x ⟶ y) : p.IsCartesian (p.map φ) φ

end CategoryTheory.Functor.IsFibered

attribute [stacks 003T "groupoid-fibration fibredness field"]
  CategoryTheory.Functor.IsFibered.InGroupoids.toIsFibered
attribute [stacks 003T "groupoid-fibration cartesian field"]
  CategoryTheory.Functor.IsFibered.InGroupoids.all_isCartesian

attribute [instance] CategoryTheory.Functor.IsFibered.InGroupoids.all_isCartesian

namespace CategoryTheory.Functor.IsFibered.InGroupoids

open CategoryTheory

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]

/-- The identity functor is canonically fibred in groupoids. -/
instance id : Functor.IsFibered.InGroupoids (Functor.id C) := sorry

/-- The opposite of an identity functor is canonically fibred in groupoids. -/
instance idOp : Functor.IsFibered.InGroupoids (Functor.id C).op :=
  inferInstanceAs (Functor.IsFibered.InGroupoids (Functor.id (Cᵒᵖ)))

/-- A functor is fibred in groupoids exactly when it is fibered and every total-category
morphism is strongly Cartesian over its image. This recognizes the canonical projection-level
owner rather than introducing a second representation of the property. -/
@[stacks 003V "(1)"]
theorem iff_isFibered_allStronglyCartesian (p : S ⥤ C) :
    Functor.IsFibered.InGroupoids p ↔
      p.IsFibered ∧ ∀ {x y : S} (φ : x ⟶ y),
        p.IsStronglyCartesian (p.map φ) φ := sorry

variable {p : S ⥤ C} [Functor.IsFibered.InGroupoids p]

/-- Every total-category morphism of a category fibred in groupoids is strongly Cartesian over
its image in the base. This is an elimination theorem rather than an instance depending on the
chosen morphism. -/
@[stacks 003V "(2)"]
theorem all_isStronglyCartesian {x y : S} (φ : x ⟶ y) :
    p.IsStronglyCartesian (p.map φ) φ := sorry

end CategoryTheory.Functor.IsFibered.InGroupoids
