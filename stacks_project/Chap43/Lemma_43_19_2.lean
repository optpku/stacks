module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Diagonal.Intersection
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : SchemeOverField k)
  (r s : ℤ)
  (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
  (beta : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s)
  (hproper : IntersectProperly
    (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
    (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta))

section

variable [Variety X] [Scheme.Regular X.left]

/- Lemma 43.19.2 (1): the exterior product of two properly intersecting cycles intersects the
diagonal cycle properly. -/
@[stacks 0B0U] #check
  (AlgebraicGeometry.AlgebraicCycle.exteriorProduct_intersectsDiagonalProperly
      X r s alpha beta hproper :
    IntersectProperly
      (CycleGroup.toAlgebraicCycle
        ((X ⨯ X).hom.relativeDimensionFunction (fun _ ↦ 0)) (r + s)
        (CycleGroup.exteriorProductPairing X X r s alpha beta))
      (diagonal X))

/- Lemma 43.19.2 (2): diagonal pushforward of the intersection equals the intersection of the
diagonal cycle with the exterior product. -/
@[stacks 0B0U] #check
  (AlgebraicGeometry.AlgebraicCycle.map_intersection_eq_diagonalIntersection
      X r s alpha beta hproper :
    AlgebraicCycle.map
      (pullback.diagonal X.hom ≫ (Over.prodLeftIsoPullback X X).inv)
        (X.hom.relativeDimensionFunction (fun _ ↦ 0))
        ((X ⨯ X).hom.relativeDimensionFunction (fun _ ↦ 0))
        (intersection
          (CycleGroup.toAlgebraicCycle
            (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
          (CycleGroup.toAlgebraicCycle
            (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta) hproper) =
      intersection (diagonal X)
        (CycleGroup.toAlgebraicCycle
          ((X ⨯ X).hom.relativeDimensionFunction (fun _ ↦ 0)) (r + s)
          (CycleGroup.exteriorProductPairing X X r s alpha beta))
        (diagonal_intersectsExteriorProductProperly X r s alpha beta hproper))

end

section

variable [ProperVariety X] [Scheme.Regular X.left]

/- Lemma 43.19.2 (3): for a proper variety, first-projection pushforward of the diagonal
intersection recovers the original intersection cycle. -/
@[stacks 0B0U] #check
  (AlgebraicGeometry.AlgebraicCycle.map_fst_diagonalIntersection_eq_intersection
      X r s alpha beta hproper :
    mapFstDiagonalIntersection X r s alpha beta hproper =
      intersection
        (CycleGroup.toAlgebraicCycle
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
        (CycleGroup.toAlgebraicCycle
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta) hproper)

end

end AlgebraicGeometry.AlgebraicCycle
