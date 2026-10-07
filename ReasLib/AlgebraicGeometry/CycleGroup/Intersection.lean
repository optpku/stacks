module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Intersection
public import ReasLib.AlgebraicGeometry.CycleGroup.Reindex
public import ReasLib.AlgebraicGeometry.CycleGroup.Fundamental
public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Product

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

/-- The graded intersection of properly intersecting cycles on a regular variety. -/
noncomputable def intersection {k : Type u} [Field k]
    (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left]
    (r s : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
    (beta : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s)
    (hproper : AlgebraicCycle.IntersectProperly
      (toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
      (toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta)) :
    CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0))
      (r + s - (X.dimension : ℤ)) :=
  ⟨AlgebraicCycle.intersection
      (toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
      (toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta) hproper,
    AlgebraicCycle.intersection_mem_dimensionSubgroup X r s alpha beta hproper⟩

/-- Forgetting the grading of a cycle-group intersection recovers the underlying
algebraic-cycle intersection. -/
theorem toAlgebraicCycle_intersection {k : Type u} [Field k]
    (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left]
    (r s : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
    (beta : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s)
    (hproper : AlgebraicCycle.IntersectProperly
      (toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
      (toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta)) :
    toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0))
        (r + s - (X.dimension : ℤ))
        (intersection X r s alpha beta hproper) =
      AlgebraicCycle.intersection
        (toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
        (toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta)
        hproper := sorry

/-- Reindex a canonical graded intersection to any propositionally equal requested degree. -/
noncomputable def intersectionIn {k : Type u} [Field k]
    (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left]
    (r s : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
    (beta : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s)
    (hproper : AlgebraicCycle.IntersectProperly
      (toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
      (toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta))
    (t : ℤ) (hdegree : r + s - (X.dimension : ℤ) = t) :
    CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) t :=
  reindex (X.hom.relativeDimensionFunction (fun _ ↦ 0)) hdegree
    (intersection X r s alpha beta hproper)

/-- Forgetting the grading after reindexing an intersection still recovers the underlying
algebraic-cycle intersection. -/
theorem toAlgebraicCycle_intersectionIn {k : Type u} [Field k]
    (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left]
    (r s : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
    (beta : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s)
    (hproper : AlgebraicCycle.IntersectProperly
      (toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
      (toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta))
    (t : ℤ) (hdegree : r + s - (X.dimension : ℤ) = t) :
    toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) t
        (intersectionIn X r s alpha beta hproper t hdegree) =
      AlgebraicCycle.intersection
        (toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
        (toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta)
        hproper := sorry

/-- The two exterior factors `alpha × [Y]` and `[X] × beta` have intersection
degree `r + s` on `X ⨯ Y`. -/
theorem exteriorIntersectionDegree {k : Type u} [Field k] [IsAlgClosed k]
    (X Y : SchemeOverField k) [Variety X] [Variety Y] (r s : ℤ) :
    (r + (Y.dimension : ℤ)) + ((X.dimension : ℤ) + s) -
      ((X ⨯ Y).dimension : ℤ) = r + s := sorry

end AlgebraicGeometry.CycleGroup
