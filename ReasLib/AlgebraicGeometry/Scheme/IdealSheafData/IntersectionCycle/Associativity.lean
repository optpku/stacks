/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Intersection
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle.Variety
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.IntersectionCycle
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.Intersection
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.Field

/-!
# Associativity of closed-subvariety intersection cycles

This module records the properness of the two iterated intersections and their
associativity under the expected triple-intersection dimension bound.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The cycle of `U` intersects the cycle `V · W` properly under the pairwise
properness and triple-intersection dimension hypotheses. -/
theorem subvarietyIntersection_leftProper (X : SchemeOverField k) [Variety X]
    [Scheme.Regular X.left] (U V W : X.left.IdealSheafData)
    [Variety (Over.mk (U.subschemeι ≫ X.hom))]
    [Variety (Over.mk (V.subschemeι ≫ X.hom))]
    [Variety (Over.mk (W.subschemeι ≫ X.hom))]
    (hUV : TopologicalSpace.Closeds.IntersectProperly U.support V.support)
    (hUW : TopologicalSpace.Closeds.IntersectProperly U.support W.support)
    (hVW : TopologicalSpace.Closeds.IntersectProperly V.support W.support)
    (hUVW : X.hom.closedSubschemeDeltaDimension (fun _ ↦ 0) ((U ⊔ V) ⊔ W) ≤
      (((dimension (Over.mk (U.subschemeι ≫ X.hom)) : ℤ) +
        (dimension (Over.mk (V.subschemeι ≫ X.hom)) : ℤ) +
        (dimension (Over.mk (W.subschemeι ≫ X.hom)) : ℤ) -
        2 * (X.dimension : ℤ)) : EInt)) :
    AlgebraicCycle.IntersectProperly (subvarietyCycle X U)
      (V.intersectionCycle W hVW) := sorry

/-- The cycle `U · V` intersects the cycle of `W` properly under the pairwise
properness and triple-intersection dimension hypotheses. -/
theorem subvarietyIntersection_rightProper (X : SchemeOverField k) [Variety X]
    [Scheme.Regular X.left] (U V W : X.left.IdealSheafData)
    [Variety (Over.mk (U.subschemeι ≫ X.hom))]
    [Variety (Over.mk (V.subschemeι ≫ X.hom))]
    [Variety (Over.mk (W.subschemeι ≫ X.hom))]
    (hUV : TopologicalSpace.Closeds.IntersectProperly U.support V.support)
    (hUW : TopologicalSpace.Closeds.IntersectProperly U.support W.support)
    (hVW : TopologicalSpace.Closeds.IntersectProperly V.support W.support)
    (hUVW : X.hom.closedSubschemeDeltaDimension (fun _ ↦ 0) ((U ⊔ V) ⊔ W) ≤
      (((dimension (Over.mk (U.subschemeι ≫ X.hom)) : ℤ) +
        (dimension (Over.mk (V.subschemeι ≫ X.hom)) : ℤ) +
        (dimension (Over.mk (W.subschemeι ≫ X.hom)) : ℤ) -
        2 * (X.dimension : ℤ)) : EInt)) :
    AlgebraicCycle.IntersectProperly (U.intersectionCycle V hUV)
      (subvarietyCycle X W) := sorry

/-- Pairwise properly intersecting closed subvarieties satisfying the expected
triple-intersection dimension bound have associative intersection cycles. -/
theorem subvarietyIntersection_assoc (X : SchemeOverField k) [Variety X]
    [Scheme.Regular X.left] (U V W : X.left.IdealSheafData)
    [Variety (Over.mk (U.subschemeι ≫ X.hom))]
    [Variety (Over.mk (V.subschemeι ≫ X.hom))]
    [Variety (Over.mk (W.subschemeι ≫ X.hom))]
    (hUV : TopologicalSpace.Closeds.IntersectProperly U.support V.support)
    (hUW : TopologicalSpace.Closeds.IntersectProperly U.support W.support)
    (hVW : TopologicalSpace.Closeds.IntersectProperly V.support W.support)
    (hUVW : X.hom.closedSubschemeDeltaDimension (fun _ ↦ 0) ((U ⊔ V) ⊔ W) ≤
      (((dimension (Over.mk (U.subschemeι ≫ X.hom)) : ℤ) +
        (dimension (Over.mk (V.subschemeι ≫ X.hom)) : ℤ) +
        (dimension (Over.mk (W.subschemeι ≫ X.hom)) : ℤ) -
        2 * (X.dimension : ℤ)) : EInt)) :
    AlgebraicCycle.intersection (subvarietyCycle X U)
        (V.intersectionCycle W hVW)
        (subvarietyIntersection_leftProper X U V W hUV hUW hVW hUVW) =
      AlgebraicCycle.intersection (U.intersectionCycle V hUV)
        (subvarietyCycle X W)
        (subvarietyIntersection_rightProper X U V W hUV hUW hVW hUVW) := sorry

end AlgebraicGeometry.SchemeOverField
