/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.ExteriorProduct.Intersection
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X Y : SchemeOverField k) [Variety X] [Variety Y]
  [Scheme.Regular X.left] [Scheme.Regular Y.left]
  (r s : ℤ)
  (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
  (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s)

/- Lemma 43.18.2 (1): pulling `beta` back along the projection to `Y` gives
the exterior product `[X] × beta`. -/
@[stacks 0B0R] #check
  (AlgebraicGeometry.CycleGroup.flatPullback_snd_eq_fundamental_exteriorProduct X Y s beta :
    reindex ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0))
        (add_comm s (X.dimension : ℤ))
        (flatPullback (fun _ ↦ 0) (X ⨯ Y) Y
          (prod.snd : X ⨯ Y ⟶ Y) X.dimension s beta) =
      exteriorProductPairing X Y (X.dimension : ℤ) s
        (fundamental (X.hom.relativeDimensionFunction (fun _ ↦ 0))
          (X.dimension : ℤ)) beta)

/- Lemma 43.18.2 (2): pulling `alpha` back along the projection to `X` gives
the exterior product `alpha × [Y]`. -/
@[stacks 0B0R] #check
  (AlgebraicGeometry.CycleGroup.flatPullback_fst_eq_exteriorProduct_fundamental X Y r alpha :
    flatPullback (fun _ ↦ 0) (X ⨯ Y) X
        (prod.fst : X ⨯ Y ⟶ X) Y.dimension r alpha =
      exteriorProductPairing X Y r (Y.dimension : ℤ) alpha
        (fundamental (Y.hom.relativeDimensionFunction (fun _ ↦ 0))
          (Y.dimension : ℤ)))

/- Lemma 43.18.2 (3): the exterior factors `alpha × [Y]` and `[X] × beta`
intersect properly on `X ⨯ Y`. -/
@[stacks 0B0R] #check
  (AlgebraicGeometry.CycleGroup.exteriorFactors_intersectProperly X Y r s alpha beta :
    AlgebraicCycle.IntersectProperly
      (toAlgebraicCycle ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0))
        (r + (Y.dimension : ℤ))
        (exteriorProductPairing X Y r (Y.dimension : ℤ) alpha
          (fundamental (Y.hom.relativeDimensionFunction (fun _ ↦ 0))
            (Y.dimension : ℤ))))
      (toAlgebraicCycle ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0))
        ((X.dimension : ℤ) + s)
        (exteriorProductPairing X Y (X.dimension : ℤ) s
          (fundamental (X.hom.relativeDimensionFunction (fun _ ↦ 0))
            (X.dimension : ℤ)) beta)))

/- Lemma 43.18.2 (4): the pullbacks along the projections to `X` and `Y`
intersect properly on `X ⨯ Y`. -/
@[stacks 0B0R] #check
  (AlgebraicGeometry.CycleGroup.projectionPullbacks_intersectProperly X Y r s alpha beta :
    AlgebraicCycle.IntersectProperly
      (toAlgebraicCycle ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0))
        (r + (Y.dimension : ℤ))
        (flatPullback (fun _ ↦ 0) (X ⨯ Y) X
          (prod.fst : X ⨯ Y ⟶ X) Y.dimension r alpha))
      (toAlgebraicCycle ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0))
        ((X.dimension : ℤ) + s)
        (reindex ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0))
          (add_comm s (X.dimension : ℤ))
          (flatPullback (fun _ ↦ 0) (X ⨯ Y) Y
            (prod.snd : X ⨯ Y ⟶ Y) X.dimension s beta))))

/- Lemma 43.18.2 (5): `alpha × beta` is the intersection of
`alpha × [Y]` with `[X] × beta` in degree `r + s`. -/
@[stacks 0B0R] #check
  (AlgebraicGeometry.CycleGroup.exteriorProduct_eq_intersection X Y r s alpha beta :
    exteriorProductPairing X Y r s alpha beta =
      intersectionIn (X ⨯ Y) (r + (Y.dimension : ℤ))
        ((X.dimension : ℤ) + s)
        (exteriorProductPairing X Y r (Y.dimension : ℤ) alpha
          (fundamental (Y.hom.relativeDimensionFunction (fun _ ↦ 0))
            (Y.dimension : ℤ)))
        (exteriorProductPairing X Y (X.dimension : ℤ) s
          (fundamental (X.hom.relativeDimensionFunction (fun _ ↦ 0))
            (X.dimension : ℤ)) beta)
        (exteriorFactors_intersectProperly X Y r s alpha beta) (r + s)
        (exteriorIntersectionDegree X Y r s))

/- Lemma 43.18.2 (6): the exterior-factor intersection equals the type-correct
intersection of the pullbacks `pr_X⁺(alpha)` and `pr_Y⁺(beta)`. -/
@[stacks 0B0R] #check
  (AlgebraicGeometry.CycleGroup.intersection_eq_projectionIntersection X Y r s alpha beta :
    intersectionIn (X ⨯ Y) (r + (Y.dimension : ℤ))
        ((X.dimension : ℤ) + s)
        (exteriorProductPairing X Y r (Y.dimension : ℤ) alpha
          (fundamental (Y.hom.relativeDimensionFunction (fun _ ↦ 0))
            (Y.dimension : ℤ)))
        (exteriorProductPairing X Y (X.dimension : ℤ) s
          (fundamental (X.hom.relativeDimensionFunction (fun _ ↦ 0))
            (X.dimension : ℤ)) beta)
        (exteriorFactors_intersectProperly X Y r s alpha beta) (r + s)
        (exteriorIntersectionDegree X Y r s) =
      intersectionIn (X ⨯ Y) (r + (Y.dimension : ℤ))
        ((X.dimension : ℤ) + s)
        (flatPullback (fun _ ↦ 0) (X ⨯ Y) X
          (prod.fst : X ⨯ Y ⟶ X) Y.dimension r alpha)
        (reindex ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0))
          (add_comm s (X.dimension : ℤ))
          (flatPullback (fun _ ↦ 0) (X ⨯ Y) Y
            (prod.snd : X ⨯ Y ⟶ Y) X.dimension s beta))
        (projectionPullbacks_intersectProperly X Y r s alpha beta) (r + s)
        (exteriorIntersectionDegree X Y r s))

end AlgebraicGeometry.CycleGroup
