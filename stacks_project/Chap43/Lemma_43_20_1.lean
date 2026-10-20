/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.IntersectionCycle.Associativity
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 43.20.1: pairwise properly intersecting closed subvarieties satisfying the
expected triple-intersection dimension bound have associative intersection cycles. -/
@[stacks 0B1L] #check
  (AlgebraicGeometry.SchemeOverField.subvarietyIntersection_assoc :
    ∀ {k : Type u} [Field k]
      (X : AlgebraicGeometry.SchemeOverField k) [Variety X] [Scheme.Regular X.left]
      (U V W : X.left.IdealSheafData)
      [Variety (Over.mk (U.subschemeι ≫ X.hom))]
      [Variety (Over.mk (V.subschemeι ≫ X.hom))]
      [Variety (Over.mk (W.subschemeι ≫ X.hom))]
      (hUV : TopologicalSpace.Closeds.IntersectProperly U.support V.support)
      (hUW : TopologicalSpace.Closeds.IntersectProperly U.support W.support)
      (hVW : TopologicalSpace.Closeds.IntersectProperly V.support W.support)
      (hUVW : X.hom.closedSubschemeDeltaDimension (fun _ ↦ 0) ((U ⊔ V) ⊔ W) ≤
        (((AlgebraicGeometry.SchemeOverField.dimension
              (Over.mk (U.subschemeι ≫ X.hom)) : ℤ) +
          (AlgebraicGeometry.SchemeOverField.dimension
              (Over.mk (V.subschemeι ≫ X.hom)) : ℤ) +
          (AlgebraicGeometry.SchemeOverField.dimension
              (Over.mk (W.subschemeι ≫ X.hom)) : ℤ) -
          2 * (X.dimension : ℤ)) : EInt)),
      AlgebraicGeometry.AlgebraicCycle.intersection
          (AlgebraicGeometry.SchemeOverField.subvarietyCycle X U)
          (V.intersectionCycle W hVW)
          (AlgebraicGeometry.SchemeOverField.subvarietyIntersection_leftProper
            X U V W hUV hUW hVW hUVW) =
        AlgebraicGeometry.AlgebraicCycle.intersection
          (U.intersectionCycle V hUV)
          (AlgebraicGeometry.SchemeOverField.subvarietyCycle X W)
          (AlgebraicGeometry.SchemeOverField.subvarietyIntersection_rightProper
            X U V W hUV hUW hVW hUVW))
