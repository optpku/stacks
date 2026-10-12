/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Types.Basic

@[expose] public section

open CategoryTheory.Limits

universe u v w

namespace CategoryTheory.GrothendieckTopology.Point

/-- A point of a site with fibers in `Type w` determines a point with fibers in
`Type (w + 1)` by applying `ULift` to its fiber functor. -/
def ulift {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (point : Point.{w} J) : Point.{w + 1} J :=
  let fiber : C ⥤ Type (w + 1) := point.fiber ⋙ uliftFunctor.{w + 1, w}
  let laws : IsCofiltered fiber.Elements ∧ InitiallySmall.{w + 1} fiber.Elements ∧
      (∀ (X : C) (R : Sieve X), R ∈ J X → ∀ x : fiber.obj X,
        ∃ (Y : C) (f : Y ⟶ X) (_ : R f) (y : fiber.obj Y), fiber.map f y = x) := sorry
  { fiber := fiber
    isCofiltered := laws.1
    initiallySmall := laws.2.1
    jointly_surjective := laws.2.2 _ }

end CategoryTheory.GrothendieckTopology.Point
