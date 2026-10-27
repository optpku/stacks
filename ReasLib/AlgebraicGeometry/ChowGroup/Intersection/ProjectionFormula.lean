/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection.Completed
public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Graph

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

variable {k : Type u} [Field k] {X Y : SchemeOverField k}
    [Smooth X.hom] [Smooth Y.hom]

/-- Proper pushforward between smooth constant-dimensional schemes satisfies the integral
intersection projection formula for the canonical smooth Gysin action. -/
theorem smoothIntersectionProduct_projection_formula_ofDimensions
    (f : X ⟶ Y) [IsProper f.left] (d e : ℕ)
    [RelativeDimension X.hom d] [RelativeDimension Y.hom e]
    (alpha : Total (fun _ ↦ 0) X) (beta : Total (fun _ ↦ 0) Y) :
    Total.map (fun _ ↦ 0) f
      (Total.smoothIntersectionProductOfDimension X d alpha
        (smoothGysinMapOfDimensions f d e beta)) =
      Total.smoothIntersectionProductOfDimension Y e
        (Total.map (fun _ ↦ 0) f alpha) beta := sorry

/-- Proper pushforward between arbitrary smooth schemes satisfies the integral intersection
projection formula on dimension-completed Chow homology. -/
theorem DimensionCompleted.intersectionProduct_projection_formula
    (f : X ⟶ Y) [IsProper f.left]
    (alpha : DimensionCompleted X) (beta : DimensionCompleted Y) :
    DimensionCompleted.map f
      (DimensionCompleted.smoothIntersectionProduct X alpha
        (DimensionCompleted.smoothGysinMap f beta)) =
      DimensionCompleted.smoothIntersectionProduct Y (DimensionCompleted.map f alpha) beta := sorry

/-- A proper morphism between smooth schemes over a field has a Gysin map, and its canonical
completed Gysin action satisfies the integral intersection projection formula. -/
theorem hasGysinMap_and_intersectionProduct_projection_formula
    (f : X ⟶ Y) [IsProper f.left]
    (alpha : DimensionCompleted X) (beta : DimensionCompleted Y) :
    BivariantClass.HasGysinMap f ∧
      DimensionCompleted.map f
        (DimensionCompleted.smoothIntersectionProduct X alpha
          (DimensionCompleted.smoothGysinMap f beta)) =
        DimensionCompleted.smoothIntersectionProduct Y (DimensionCompleted.map f alpha) beta :=
  ⟨BivariantClass.hasGysinMap_of_smooth f,
    DimensionCompleted.intersectionProduct_projection_formula f alpha beta⟩

end AlgebraicGeometry.ChowGroup
