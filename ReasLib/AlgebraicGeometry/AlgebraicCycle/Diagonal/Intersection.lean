/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Diagonal
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Intersection
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Pushforward
public import ReasLib.AlgebraicGeometry.CycleGroup.ExteriorProduct
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Product.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Properties

/-!
# Intersections with diagonal cycles

This file relates the intersection of cycles on a regular variety to the intersection of their
exterior product with the diagonal cycle.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The exterior product of two properly intersecting cycles on a regular variety intersects
the diagonal cycle properly. -/
theorem exteriorProduct_intersectsDiagonalProperly
    (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left]
    (r s : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
    (beta : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s)
    (hproper : IntersectProperly
      (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
      (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta)) :
    IntersectProperly
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ X).hom.relativeDimensionFunction (fun _ ↦ 0)) (r + s)
        (CycleGroup.exteriorProductPairing X X r s alpha beta))
      (diagonal X) := sorry

/-- The diagonal cycle intersects the exterior product of two properly intersecting cycles
properly. -/
theorem diagonal_intersectsExteriorProductProperly
    (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left]
    (r s : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
    (beta : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s)
    (hproper : IntersectProperly
      (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
      (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta)) :
    IntersectProperly (diagonal X)
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ X).hom.relativeDimensionFunction (fun _ ↦ 0)) (r + s)
        (CycleGroup.exteriorProductPairing X X r s alpha beta)) := sorry

/-- Pushing the intersection of two cycles along the diagonal equals the intersection of the
diagonal cycle with their exterior product. -/
theorem map_intersection_eq_diagonalIntersection
    (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left]
    (r s : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
    (beta : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s)
    (hproper : IntersectProperly
      (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
      (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta)) :
    AlgebraicCycle.map
      (pullback.diagonal X.hom ≫ (Over.prodLeftIsoPullback X X).inv)
        (X.hom.relativeDimensionFunction (fun _ ↦ 0))
        ((X ⨯ X).hom.relativeDimensionFunction (fun _ ↦ 0))
        (intersection
          (CycleGroup.toAlgebraicCycle
            (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
          (CycleGroup.toAlgebraicCycle
            (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta) hproper) =
      @intersection _ (SchemeOverField.regularProdOfRegular X X) (diagonal X)
        (CycleGroup.toAlgebraicCycle
          ((X ⨯ X).hom.relativeDimensionFunction (fun _ ↦ 0)) (r + s)
          (CycleGroup.exteriorProductPairing X X r s alpha beta))
        (diagonal_intersectsExteriorProductProperly X r s alpha beta hproper) := sorry

/-- The pushforward along the first projection of the intersection of the diagonal cycle with
the exterior product of two properly intersecting cycles. -/
noncomputable def mapFstDiagonalIntersection
    (X : SchemeOverField k) [ProperVariety X] [Scheme.Regular X.left]
    (r s : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
    (beta : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s)
    (hproper : IntersectProperly
      (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
      (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta)) :
    AlgebraicCycle X.left ℤ := by
  -- Local instance justification (proof-local temporary data): properness is needed only to construct this explicit pushforward.
  letI : IsProper (Over.Hom.left (prod.fst : X ⨯ X ⟶ X)) :=
    SchemeOverField.prodFstIsProper X X
  exact AlgebraicCycle.map (Over.Hom.left (prod.fst : X ⨯ X ⟶ X))
    ((X ⨯ X).hom.relativeDimensionFunction (fun _ ↦ 0))
    (X.hom.relativeDimensionFunction (fun _ ↦ 0))
    (@intersection _ (SchemeOverField.regularProdOfRegular X X) (diagonal X)
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ X).hom.relativeDimensionFunction (fun _ ↦ 0)) (r + s)
        (CycleGroup.exteriorProductPairing X X r s alpha beta))
      (diagonal_intersectsExteriorProductProperly X r s alpha beta hproper))

/-- For a proper regular variety, pushing the diagonal intersection along the first projection
recovers the intersection of the original cycles. -/
theorem map_fst_diagonalIntersection_eq_intersection
    (X : SchemeOverField k) [ProperVariety X] [Scheme.Regular X.left]
    (r s : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
    (beta : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s)
    (hproper : IntersectProperly
      (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
      (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta)) :
    mapFstDiagonalIntersection X r s alpha beta hproper =
      intersection
        (CycleGroup.toAlgebraicCycle
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
        (CycleGroup.toAlgebraicCycle
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta) hproper := sorry

end AlgebraicGeometry.AlgebraicCycle
