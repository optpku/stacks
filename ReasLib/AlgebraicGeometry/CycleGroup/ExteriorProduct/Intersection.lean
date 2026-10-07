module

public import ReasLib.AlgebraicGeometry.CycleGroup.Intersection
public import ReasLib.AlgebraicGeometry.CycleGroup.ExteriorProduct
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.CycleGroup.Fundamental
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Product

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

/-- The second projection flat pullback of a fundamental cycle is the corresponding
exterior product. -/
theorem flatPullback_snd_eq_fundamental_exteriorProduct :
    reindex ((X ⨯ Y).hom.relativeDimensionFunction (fun _ ↦ 0))
        (add_comm s (X.dimension : ℤ))
        (flatPullback (fun _ ↦ 0) (X ⨯ Y) Y
          (prod.snd : X ⨯ Y ⟶ Y) X.dimension s beta) =
      exteriorProductPairing X Y (X.dimension : ℤ) s
        (fundamental (X.hom.relativeDimensionFunction (fun _ ↦ 0))
          (X.dimension : ℤ)) beta := sorry

/-- The first projection flat pullback of a cycle is its exterior product with the
fundamental cycle of the second factor. -/
theorem flatPullback_fst_eq_exteriorProduct_fundamental :
    flatPullback (fun _ ↦ 0) (X ⨯ Y) X
        (prod.fst : X ⨯ Y ⟶ X) Y.dimension r alpha =
      exteriorProductPairing X Y r (Y.dimension : ℤ) alpha
        (fundamental (Y.hom.relativeDimensionFunction (fun _ ↦ 0))
          (Y.dimension : ℤ)) := sorry

/-- The two exterior factors intersect properly on the product. -/
theorem exteriorFactors_intersectProperly :
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
            (X.dimension : ℤ)) beta)) := sorry

/-- The two projection flat pullbacks intersect properly on the product. -/
theorem projectionPullbacks_intersectProperly :
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
            (prod.snd : X ⨯ Y ⟶ Y) X.dimension s beta))) := sorry

/-- The exterior product equals the intersection of the two exterior factors. -/
theorem exteriorProduct_eq_intersection :
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
        (exteriorIntersectionDegree X Y r s) := sorry

/-- The exterior-factor intersection equals the type-correct intersection of the
projection flat pullbacks. -/
theorem intersection_eq_projectionIntersection :
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
        (exteriorIntersectionDegree X Y r s) := sorry

end AlgebraicGeometry.CycleGroup
