module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.ProperIntersection
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.LocallyFiniteSum
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.IntersectionCycle
public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Product

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable {X : Scheme.{u}}

/-- Properly intersecting cycles give properly intersecting reduced closures at every pair
of points carrying nonzero coefficients. -/
theorem pointClosureIntersectsProperly (alpha beta : AlgebraicCycle X ℤ)
    (hproper : alpha.IntersectProperly beta) (x y : X)
    (hx : alpha x ≠ 0) (hy : beta y ≠ 0) :
    TopologicalSpace.Closeds.IntersectProperly
      (Scheme.PointClosure.reducedStructure x).ideal.support
      (Scheme.PointClosure.reducedStructure y).ideal.support := sorry

/-- The contribution of a pair of components to the intersection of two properly
intersecting cycles. -/
noncomputable def intersectionTerm [Scheme.Regular X]
    (alpha beta : AlgebraicCycle X ℤ) (hproper : alpha.IntersectProperly beta)
    (x y : X) : AlgebraicCycle X ℤ :=
  if hx : alpha x ≠ 0 then
    if hy : beta y ≠ 0 then
      (alpha x * beta y) •
        Scheme.IdealSheafData.intersectionCycle
          (Scheme.PointClosure.reducedStructure x).ideal
          (Scheme.PointClosure.reducedStructure y).ideal
          (pointClosureIntersectsProperly alpha beta hproper x y hx hy)
    else 0
  else 0

/-- The component-pair terms defining cycle intersection have locally finite support. -/
theorem intersectionTermsLocallyFinite [Scheme.Regular X]
    (alpha beta : AlgebraicCycle X ℤ) (hproper : alpha.IntersectProperly beta) :
    LocallyFinite fun p : X × X ↦
      (intersectionTerm alpha beta hproper p.1 p.2).support := sorry

/-- The intersection of properly intersecting algebraic cycles, formed as the explicit
locally finite sum of their componentwise Serre intersection cycles. -/
noncomputable def intersection [Scheme.Regular X]
    (alpha beta : AlgebraicCycle X ℤ) (hproper : alpha.IntersectProperly beta) :
    AlgebraicCycle X ℤ :=
  locallyFiniteSum
    (fun p : X × X ↦ intersectionTerm alpha beta hproper p.1 p.2)
    (intersectionTermsLocallyFinite alpha beta hproper)

/-- The coefficient of a cycle intersection is the finite sum of the corresponding
component-pair intersection coefficients. -/
theorem intersection_apply [Scheme.Regular X]
    (alpha beta : AlgebraicCycle X ℤ) (hproper : alpha.IntersectProperly beta) (z : X) :
    intersection alpha beta hproper z =
      ∑ᶠ p : X × X, intersectionTerm alpha beta hproper p.1 p.2 z := sorry

/-- Intersecting degree-`r` and degree-`s` cycles on a regular variety produces a cycle
of degree `r + s - X.dimension`. -/
theorem intersection_mem_dimensionSubgroup {k : Type u} [Field k]
    (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left]
    (r s : ℤ)
    (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
    (beta : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s)
    (hproper : IntersectProperly
      (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
      (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta)) :
    intersection
        (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
        (CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta)
        hproper ∈
      dimensionSubgroup (X.hom.relativeDimensionFunction (fun _ ↦ 0))
        (r + s - (X.dimension : ℤ)) := sorry

end AlgebraicGeometry.AlgebraicCycle
