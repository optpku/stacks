/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.Intersection
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.AssociatedCycle.Variety

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
  (X Y : SchemeOverField k) [Variety X] [Variety Y]
  [Scheme.Regular X.left] [Scheme.Regular Y.left]
  (f : X ⟶ Y) [Flat f.left]
  (F G : Y.left.Modules) [F.IsCoherent] [G.IsCoherent]
  (r s : ℤ)

/-- Under the expected support-dimension bounds, the associated cycles of two coherent
modules pulled back along a flat morphism of regular varieties intersect properly. -/
theorem pullbackAssociatedCycles_intersectProperly
    (hF : ∀ y ∈ RingedSpace.moduleSupport F,
      Y.hom.relativeDimensionFunction (fun _ ↦ 0) y ≤ r)
    (hG : ∀ y ∈ RingedSpace.moduleSupport G,
      Y.hom.relativeDimensionFunction (fun _ ↦ 0) y ≤ s)
    (hFG : ∀ y ∈ RingedSpace.moduleSupport F ∩ RingedSpace.moduleSupport G,
      Y.hom.relativeDimensionFunction (fun _ ↦ 0) y ≤
        r + s - (Y.dimension : ℤ)) :
    AlgebraicCycle.IntersectProperly
      (((Scheme.Modules.pullback f.left).obj F).associatedCycle
        (X.hom.relativeDimensionFunction (fun _ ↦ 0))
        (r + (relativeDimensionGap X Y f : ℤ)))
      (((Scheme.Modules.pullback f.left).obj G).associatedCycle
        (X.hom.relativeDimensionFunction (fun _ ↦ 0))
        (s + (relativeDimensionGap X Y f : ℤ))) := sorry

/-- Flat pullback commutes with the intersection of associated cycles of coherent modules
on regular varieties when their supports satisfy the proper-intersection bounds. -/
theorem flatPullback_intersection_associatedCycles
    (hF : ∀ y ∈ RingedSpace.moduleSupport F,
      Y.hom.relativeDimensionFunction (fun _ ↦ 0) y ≤ r)
    (hG : ∀ y ∈ RingedSpace.moduleSupport G,
      Y.hom.relativeDimensionFunction (fun _ ↦ 0) y ≤ s)
    (hFG : ∀ y ∈ RingedSpace.moduleSupport F ∩ RingedSpace.moduleSupport G,
      Y.hom.relativeDimensionFunction (fun _ ↦ 0) y ≤
        r + s - (Y.dimension : ℤ)) :
    AlgebraicCycle.flatPullback (fun _ ↦ 0) X Y f (relativeDimensionGap X Y f)
        (r + s - (Y.dimension : ℤ) + (relativeDimensionGap X Y f : ℤ))
        (AlgebraicCycle.intersection
          (F.associatedCycle (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
          (G.associatedCycle (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s)
          (associatedCycles_intersectProperly Y F G r s hF hG hFG)) =
      AlgebraicCycle.intersection
        (((Scheme.Modules.pullback f.left).obj F).associatedCycle
          (X.hom.relativeDimensionFunction (fun _ ↦ 0))
          (r + (relativeDimensionGap X Y f : ℤ)))
        (((Scheme.Modules.pullback f.left).obj G).associatedCycle
          (X.hom.relativeDimensionFunction (fun _ ↦ 0))
          (s + (relativeDimensionGap X Y f : ℤ)))
        (pullbackAssociatedCycles_intersectProperly X Y f F G r s hF hG hFG) := sorry

end AlgebraicGeometry.SchemeOverField
