/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Intersection
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Pushforward
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Variety
public import ReasLib.RingTheory.Catenary.Field

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable {k : Type u} [Field k]
  (X Y : SchemeOverField k) [Variety X] [Variety Y]
  [Scheme.Regular X.left] [Scheme.Regular Y.left]
  (f : X ⟶ Y) [Flat f.left] [IsProper f.left]
  (r s : ℤ)
  (alpha : CycleGroup X.left (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
  (beta : CycleGroup Y.left (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s)

/-- For a flat proper morphism of regular varieties, proper intersection with the flat pullback
at the canonical relative-dimension gap implies proper intersection after pushforward. -/
theorem map_intersectProperly_flatPullback
    (hproper : IntersectProperly
      (CycleGroup.toAlgebraicCycle
        (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
      (flatPullback (fun _ ↦ 0) X Y f (SchemeOverField.relativeDimensionGap X Y f)
        (s + (SchemeOverField.relativeDimensionGap X Y f : ℤ))
        (CycleGroup.toAlgebraicCycle
          (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta))) :
    IntersectProperly
      (map f.left (X.hom.relativeDimensionFunction (fun _ ↦ 0))
        (Y.hom.relativeDimensionFunction (fun _ ↦ 0))
        (CycleGroup.toAlgebraicCycle
          (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha))
      (CycleGroup.toAlgebraicCycle
        (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta) := sorry

/-- Under proper intersection with the flat pullback at the canonical relative-dimension gap,
pushforward along a flat proper morphism commutes with intersection against a target cycle. -/
theorem map_intersection_flatPullback
    (hproper : IntersectProperly
      (CycleGroup.toAlgebraicCycle
        (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
      (flatPullback (fun _ ↦ 0) X Y f (SchemeOverField.relativeDimensionGap X Y f)
        (s + (SchemeOverField.relativeDimensionGap X Y f : ℤ))
        (CycleGroup.toAlgebraicCycle
          (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta))) :
    intersection
        (map f.left (X.hom.relativeDimensionFunction (fun _ ↦ 0))
          (Y.hom.relativeDimensionFunction (fun _ ↦ 0))
          (CycleGroup.toAlgebraicCycle
            (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha))
        (CycleGroup.toAlgebraicCycle
          (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta)
        (map_intersectProperly_flatPullback X Y f r s alpha beta hproper) =
      map f.left (X.hom.relativeDimensionFunction (fun _ ↦ 0))
        (Y.hom.relativeDimensionFunction (fun _ ↦ 0))
        (intersection
          (CycleGroup.toAlgebraicCycle
            (X.hom.relativeDimensionFunction (fun _ ↦ 0)) r alpha)
          (flatPullback (fun _ ↦ 0) X Y f (SchemeOverField.relativeDimensionGap X Y f)
            (s + (SchemeOverField.relativeDimensionGap X Y f : ℤ))
            (CycleGroup.toAlgebraicCycle
              (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s beta))
          hproper) := sorry

end AlgebraicGeometry.AlgebraicCycle
