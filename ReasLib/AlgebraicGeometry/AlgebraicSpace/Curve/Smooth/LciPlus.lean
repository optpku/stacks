/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Smooth.StructureMorphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.LocalCompleteIntersection.IsolatedSingularities
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.DeligneMumford
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Points

/-!
# Inclusion of smooth curves into local complete intersection curves

Smooth families form an open substack of local complete intersection families
with isolated singularities. The canonical inclusion induces their image on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- Membership in `smooth` implies membership in `lciPlus`. -/
theorem smooth_le_lciPlus (S : Scheme.{u}) : smooth S ≤ lciPlus S := sorry

/-- The full subcategory of `𝒞urves` cut out by `smooth` is an algebraic stack in
the Hom-universe of `CohStack.toGroupoids`. -/
instance instAlgebraicStack_ofObjectProperty_smooth (S : Scheme.{u}) :
    CohStack.AlgebraicStack (ofObjectProperty (smooth S)) :=
  sorry

/-- The full subcategory of `𝒞urves` cut out by `lciPlus` is an algebraic stack in
the Hom-universe of `CohStack.toGroupoids`. -/
instance instAlgebraicStack_ofObjectProperty_lciPlus (S : Scheme.{u}) :
    CohStack.AlgebraicStack (ofObjectProperty (lciPlus S)) :=
  sorry

/-- The inclusion of `𝒞urves^{smooth}` into `𝒞urves` is an open immersion. -/
instance instOpenImmersion_inclusionOf_smooth (S : Scheme.{u}) :
    CohStack.OpenImmersion (inclusionOf (smooth S)) :=
  sorry

/-- The full-subcategory inclusion of smooth families into local complete
intersection families with isolated singularities commutes with projection to
the base scheme. -/
private theorem inclusionSmoothLciPlus_comm (S : Scheme.{u}) :
    ιOfLE (smooth_le_lciPlus S) ⋙ (ofObjectProperty (lciPlus S)).p =
      (ofObjectProperty (smooth S)).p := sorry

/-- The inclusion of `𝒞urves^{smooth}` into `𝒞urves^{lci+}`, as a 1-morphism of
categories fibred in groupoids over `Over S`. -/
def inclusionSmoothLciPlus (S : Scheme.{u}) :
    ofObjectProperty (smooth S) ⟶ ofObjectProperty (lciPlus S) :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    { toFunctor := ιOfLE (smooth_le_lciPlus S)
      w := by exact inclusionSmoothLciPlus_comm S }

/-- The underlying functor of `inclusionSmoothLciPlus S` is the identity-on-carriers
map of `smooth_le_lciPlus`. -/
theorem inclusionSmoothLciPlus_toFunctor (S : Scheme.{u}) :
    FiberedCategoryOver.Groupoids.toFunctor (inclusionSmoothLciPlus S) =
      ιOfLE (smooth_le_lciPlus S) :=
  rfl

/-- The inclusion of `𝒞urves^{smooth}` into `𝒞urves^{lci+}` is an open immersion. -/
instance instOpenImmersion_inclusionSmoothLciPlus (S : Scheme.{u}) :
    CohStack.OpenImmersion (inclusionSmoothLciPlus S) :=
  sorry

/-- The set of points of `𝒞urves^{lci+}` in the image of
`|𝒞urves^{smooth}| → |𝒞urves^{lci+}|`. -/
def smoothPointsSet (S : Scheme.{u}) :
    Set (CohStack.Points (ofObjectProperty (lciPlus S))) :=
  Set.range (CohStack.Points.map (inclusionSmoothLciPlus S))

/-- `smoothPointsSet S` is the range of `CohStack.Points.map` of
`inclusionSmoothLciPlus S`. -/
theorem smoothPointsSet_eq (S : Scheme.{u}) :
    smoothPointsSet S =
      Set.range (CohStack.Points.map (inclusionSmoothLciPlus S)) :=
  rfl

/-- A point of `|𝒞urves^{lci+}|` lies in `smoothPointsSet S` if and only if it is
the image of a point of `|𝒞urves^{smooth}|`. -/
theorem mem_smoothPointsSet (S : Scheme.{u})
    {x : CohStack.Points (ofObjectProperty (lciPlus S))} :
    x ∈ smoothPointsSet S ↔
      ∃ y : CohStack.Points (ofObjectProperty (smooth S)),
        CohStack.Points.map (inclusionSmoothLciPlus S) y = x :=
  Iff.rfl

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
