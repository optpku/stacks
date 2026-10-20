module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Categories with common successors

This module isolates the object-level part of filteredness: any two objects admit maps to a
common successor. It is useful when a construction needs no compatibility for parallel maps.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory

/-- A chosen common successor of two objects, together with the two structure maps. -/
@[stacks 09WQ "common successor data"]
structure CommonSuccessor {I : Type u} [Category.{v} I] (X Y : I) where
  /-- The common successor object. -/
  obj : I
  /-- The structure map from the first object. -/
  left : X ⟶ obj
  /-- The structure map from the second object. -/
  right : Y ⟶ obj

namespace CommonSuccessor

variable {I : Type u} [Category.{v} I] {W X Y Z : I}

/-- Exchange the two inputs of a common successor. -/
def swap (s : CommonSuccessor X Y) : CommonSuccessor Y X where
  obj := s.obj
  left := s.right
  right := s.left

/-- Precompose both legs of a common successor. -/
def precomp (s : CommonSuccessor X Y) (f : W ⟶ X) (g : Z ⟶ Y) :
    CommonSuccessor W Z where
  obj := s.obj
  left := f ≫ s.left
  right := g ≫ s.right

end CommonSuccessor

/-- A category has common successors if every two objects admit maps to a third object. -/
@[stacks 09WQ "categories with common successors"]
class HasCommonSuccessors (I : Type u) [Category.{v} I] : Prop where
  /-- Every pair of objects has a common successor. -/
  nonempty (X Y : I) : Nonempty (CommonSuccessor X Y)

variable {I : Type u} [Category.{v} I]

namespace HasCommonSuccessors

/-- The selected bundled cospan witnessing that `X` and `Y` have a common successor. This is the
single choice boundary for clients that need the successor and both structure maps as data. -/
@[stacks 09WQ "selected common successor cospan"]
noncomputable def cospan [HasCommonSuccessors I] (X Y : I) : CommonSuccessor X Y :=
  Classical.choice (HasCommonSuccessors.nonempty X Y)

end HasCommonSuccessors

namespace CommonSuccessor

/-- A common-successor cospan exists exactly when its apex and two maps can be specified. -/
theorem nonempty_iff (X Y : I) :
    Nonempty (CommonSuccessor X Y) ↔
      ∃ (Z : I), Nonempty (X ⟶ Z) ∧ Nonempty (Y ⟶ Z) := sorry

end CommonSuccessor

/-- The class of common successors is equivalent to its explicit objectwise condition. -/
@[stacks 09WQ "common successor criterion"]
theorem hasCommonSuccessors_iff :
    HasCommonSuccessors I ↔
      ∀ X Y : I, ∃ (Z : I), Nonempty (X ⟶ Z) ∧ Nonempty (Y ⟶ Z) := sorry

/-- Construct common-successor data from the corresponding explicit condition. -/
theorem HasCommonSuccessors.of
    (h : ∀ X Y : I, ∃ (Z : I), Nonempty (X ⟶ Z) ∧ Nonempty (Y ⟶ Z)) :
    HasCommonSuccessors I := sorry

/-- Every pair of objects in a category with common successors maps to a common object. -/
theorem HasCommonSuccessors.exists
    [HasCommonSuccessors I] (X Y : I) :
    ∃ (Z : I), Nonempty (X ⟶ Z) ∧ Nonempty (Y ⟶ Z) := sorry

/-- A filtered-or-empty category has common successors. -/
instance hasCommonSuccessors_of_isFilteredOrEmpty
    [IsFilteredOrEmpty I] : HasCommonSuccessors I := sorry

end CategoryTheory
