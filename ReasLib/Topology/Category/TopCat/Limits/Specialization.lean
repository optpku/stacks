module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Inseparable

/-!
# Specialization in limits of topological spaces

This file relates specialization in the vertex of a limiting cone to
specialization after its projection maps.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace TopCat.IsLimit

variable {J : Type v} [Category.{w} J] {F : J ⥤ TopCat.{u}}

/-- Failure of specialization in the vertex of a limiting cone of topological
spaces is detected by one of the cone projections. -/
theorem exists_not_specializes (C : Cone F) (hC : CategoryTheory.Limits.IsLimit C)
    (x y : C.pt) :
    ¬ x ⤳ y → ∃ j : J, ¬ C.π.app j x ⤳ C.π.app j y := sorry

end TopCat.IsLimit
