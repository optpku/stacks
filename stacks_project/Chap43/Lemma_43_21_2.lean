/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.FlatPullback.Intersection

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 43.21.2 (1): flat pullback along a flat morphism of nonsingular varieties
preserves proper intersection of graded algebraic cycles. -/
@[stacks 0B0Z] #check
  (AlgebraicGeometry.AlgebraicCycle.flatPullbacks_intersectProperly :
    ∀ {k : Type u} [Field k]
      (X Y : SchemeOverField k) [Variety X] [Variety Y]
      [Scheme.Regular X.left] [Scheme.Regular Y.left]
      (f : X ⟶ Y) [Flat f.left] (r s : ℤ)
      (alpha : CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
      (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s)
      (hproper : AlgebraicCycle.IntersectProperly
        (CycleGroup.toAlgebraicCycle
          (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
        (CycleGroup.toAlgebraicCycle
          (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta)),
      AlgebraicCycle.IntersectProperly
        (AlgebraicCycle.flatPullback (fun _ ↦ 0) X Y f
          (SchemeOverField.relativeDimensionGap X Y f)
          (r + (SchemeOverField.relativeDimensionGap X Y f : ℤ))
          (CycleGroup.toAlgebraicCycle
            (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha))
        (AlgebraicCycle.flatPullback (fun _ ↦ 0) X Y f
          (SchemeOverField.relativeDimensionGap X Y f)
          (s + (SchemeOverField.relativeDimensionGap X Y f : ℤ))
          (CycleGroup.toAlgebraicCycle
            (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta)))

/- Lemma 43.21.2 (2): flat pullback along a flat morphism of nonsingular varieties
commutes with the intersection product of properly intersecting graded cycles. -/
@[stacks 0B0Z] #check
  (AlgebraicGeometry.AlgebraicCycle.flatPullback_intersection :
    ∀ {k : Type u} [Field k]
      (X Y : SchemeOverField k) [Variety X] [Variety Y]
      [Scheme.Regular X.left] [Scheme.Regular Y.left]
      (f : X ⟶ Y) [Flat f.left] (r s : ℤ)
      (alpha : CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
      (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s)
      (hproper : AlgebraicCycle.IntersectProperly
        (CycleGroup.toAlgebraicCycle
          (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
        (CycleGroup.toAlgebraicCycle
          (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta)),
      AlgebraicCycle.flatPullback (fun _ ↦ 0) X Y f
          (SchemeOverField.relativeDimensionGap X Y f)
          (r + s - (Y.dimension : ℤ) +
            (SchemeOverField.relativeDimensionGap X Y f : ℤ))
          (AlgebraicCycle.intersection
            (CycleGroup.toAlgebraicCycle
              (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
            (CycleGroup.toAlgebraicCycle
              (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta)
            hproper) =
        AlgebraicCycle.intersection
          (AlgebraicCycle.flatPullback (fun _ ↦ 0) X Y f
            (SchemeOverField.relativeDimensionGap X Y f)
            (r + (SchemeOverField.relativeDimensionGap X Y f : ℤ))
            (CycleGroup.toAlgebraicCycle
              (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha))
          (AlgebraicCycle.flatPullback (fun _ ↦ 0) X Y f
            (SchemeOverField.relativeDimensionGap X Y f)
            (s + (SchemeOverField.relativeDimensionGap X Y f : ℤ))
            (CycleGroup.toAlgebraicCycle
              (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta))
          (AlgebraicGeometry.AlgebraicCycle.flatPullbacks_intersectProperly
            X Y f r s alpha beta hproper))
