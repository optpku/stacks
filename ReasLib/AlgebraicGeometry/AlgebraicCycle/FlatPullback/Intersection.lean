/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.Intersection.FlatPullback

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable {k : Type u} [Field k]
  (X Y : SchemeOverField k) [Variety X] [Variety Y]
  [Scheme.Regular X.left] [Scheme.Regular Y.left]
  (f : X ⟶ Y) [Flat f.left]
  (r s : ℤ)
  (alpha : CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
  (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s)

/-- Flat pullback along a flat morphism of regular varieties preserves proper intersection
of graded algebraic cycles. -/
theorem flatPullbacks_intersectProperly
    (hproper : IntersectProperly
      (CycleGroup.toAlgebraicCycle
        (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
      (CycleGroup.toAlgebraicCycle
        (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta)) :
    IntersectProperly
      (flatPullback (fun _ ↦ 0) X Y f (SchemeOverField.relativeDimensionGap X Y f)
        (r + (SchemeOverField.relativeDimensionGap X Y f : ℤ))
        (CycleGroup.toAlgebraicCycle
          (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha))
      (flatPullback (fun _ ↦ 0) X Y f (SchemeOverField.relativeDimensionGap X Y f)
        (s + (SchemeOverField.relativeDimensionGap X Y f : ℤ))
        (CycleGroup.toAlgebraicCycle
          (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta)) := sorry

/-- Flat pullback along a flat morphism of regular varieties commutes with the intersection
product of properly intersecting graded algebraic cycles. -/
theorem flatPullback_intersection
    (hproper : IntersectProperly
      (CycleGroup.toAlgebraicCycle
        (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
      (CycleGroup.toAlgebraicCycle
        (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta)) :
    flatPullback (fun _ ↦ 0) X Y f (SchemeOverField.relativeDimensionGap X Y f)
        (r + s - (Y.dimension : ℤ) +
          (SchemeOverField.relativeDimensionGap X Y f : ℤ))
        (intersection
          (CycleGroup.toAlgebraicCycle
            (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
          (CycleGroup.toAlgebraicCycle
            (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta)
          hproper) =
      intersection
        (flatPullback (fun _ ↦ 0) X Y f (SchemeOverField.relativeDimensionGap X Y f)
          (r + (SchemeOverField.relativeDimensionGap X Y f : ℤ))
          (CycleGroup.toAlgebraicCycle
            (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha))
        (flatPullback (fun _ ↦ 0) X Y f (SchemeOverField.relativeDimensionGap X Y f)
          (s + (SchemeOverField.relativeDimensionGap X Y f : ℤ))
          (CycleGroup.toAlgebraicCycle
            (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta))
        (flatPullbacks_intersectProperly X Y f r s alpha beta hproper) := sorry

end AlgebraicGeometry.AlgebraicCycle
