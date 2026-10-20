module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Cartesian morphisms of simplicial objects

A morphism of simplicial objects is cartesian when every simplex-operator
naturality square is a pullback.
-/

@[expose]
public section

open CategoryTheory Limits Opposite

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- A morphism of simplicial objects is cartesian, equivalently the source is cartesian over
the target, when every simplex-operator naturality square is a fibre square. -/
class IsCartesian {Y X : SimplicialObject C} (a : Y ⟶ X) : Prop where
  /-- Each simplex-operator naturality square is a fibre square. -/
  isPullback {n m : SimplexCategory} (φ : n ⟶ m) :
    IsPullback (a.app (op m)) (Y.map φ.op) (X.map φ.op) (a.app (op n))

/-- A morphism of simplicial objects is cartesian iff every simplex-operator naturality square
is a fibre square. -/
theorem isCartesian_iff {Y X : SimplicialObject C} (a : Y ⟶ X) :
    IsCartesian a ↔
      ∀ {n m : SimplexCategory} (φ : n ⟶ m),
        IsPullback (a.app (op m)) (Y.map φ.op) (X.map φ.op) (a.app (op n)) := sorry

/-- A morphism of simplicial objects is cartesian iff every functoriality square on
`SimplexCategoryᵒᵖ` is a fibre square. -/
theorem isCartesian_iff_map {Y X : SimplicialObject C} (a : Y ⟶ X) :
    IsCartesian a ↔
      ∀ {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m),
        IsPullback (a.app n) (Y.map f) (X.map f) (a.app m) := sorry

/-- The identity morphism of a simplicial object is cartesian. -/
instance IsCartesian.id {X : SimplicialObject C} : IsCartesian (𝟙 X) := sorry

end CategoryTheory.SimplicialObject
