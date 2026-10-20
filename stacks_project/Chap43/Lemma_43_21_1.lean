/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.Intersection.FlatPullback

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 43.21.1 (1): the associated cycles of two coherent modules pulled back along a
flat morphism of nonsingular varieties intersect properly under the stated support bounds. -/
@[stacks 0B0Y] #check
  (AlgebraicGeometry.SchemeOverField.pullbackAssociatedCycles_intersectProperly :
    ∀ {k : Type u} [Field k]
      (X Y : SchemeOverField k) [Variety X] [Variety Y]
      [Scheme.Regular X.left] [Scheme.Regular Y.left]
      (f : X ⟶ Y) [Flat f.left]
      (F G : Y.left.Modules) [F.IsCoherent] [G.IsCoherent] (r s : ℤ)
      (hF : ∀ y ∈ RingedSpace.moduleSupport F,
        Y.hom.relativeDimensionFunction (fun _ ↦ 0) y ≤ r)
      (hG : ∀ y ∈ RingedSpace.moduleSupport G,
        Y.hom.relativeDimensionFunction (fun _ ↦ 0) y ≤ s)
      (hFG : ∀ y ∈ RingedSpace.moduleSupport F ∩ RingedSpace.moduleSupport G,
        Y.hom.relativeDimensionFunction (fun _ ↦ 0) y ≤
          r + s - (Y.dimension : ℤ)),
      AlgebraicCycle.IntersectProperly
        (((Scheme.Modules.pullback f.left).obj F).associatedCycle
          (X.hom.relativeDimensionFunction (fun _ ↦ 0))
          (r + (SchemeOverField.relativeDimensionGap X Y f : ℤ)))
        (((Scheme.Modules.pullback f.left).obj G).associatedCycle
          (X.hom.relativeDimensionFunction (fun _ ↦ 0))
          (s + (SchemeOverField.relativeDimensionGap X Y f : ℤ))))

/- Lemma 43.21.1 (2): flat pullback carries the intersection of the associated cycles to
the intersection of the associated cycles of the pulled-back coherent modules. -/
@[stacks 0B0Y] #check
  (AlgebraicGeometry.SchemeOverField.flatPullback_intersection_associatedCycles :
    ∀ {k : Type u} [Field k]
      (X Y : SchemeOverField k) [Variety X] [Variety Y]
      [Scheme.Regular X.left] [Scheme.Regular Y.left]
      (f : X ⟶ Y) [Flat f.left]
      (F G : Y.left.Modules) [F.IsCoherent] [G.IsCoherent] (r s : ℤ)
      (hF : ∀ y ∈ RingedSpace.moduleSupport F,
        Y.hom.relativeDimensionFunction (fun _ ↦ 0) y ≤ r)
      (hG : ∀ y ∈ RingedSpace.moduleSupport G,
        Y.hom.relativeDimensionFunction (fun _ ↦ 0) y ≤ s)
      (hFG : ∀ y ∈ RingedSpace.moduleSupport F ∩ RingedSpace.moduleSupport G,
        Y.hom.relativeDimensionFunction (fun _ ↦ 0) y ≤
          r + s - (Y.dimension : ℤ)),
      AlgebraicCycle.flatPullback (fun _ ↦ 0) X Y f
          (SchemeOverField.relativeDimensionGap X Y f)
          (r + s - (Y.dimension : ℤ) +
            (SchemeOverField.relativeDimensionGap X Y f : ℤ))
          (AlgebraicCycle.intersection
            (F.associatedCycle (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) r)
            (G.associatedCycle (Y.hom.relativeDimensionFunction (fun _ ↦ 0)) s)
            (AlgebraicGeometry.SchemeOverField.associatedCycles_intersectProperly
              Y F G r s hF hG hFG)) =
        AlgebraicCycle.intersection
          (((Scheme.Modules.pullback f.left).obj F).associatedCycle
            (X.hom.relativeDimensionFunction (fun _ ↦ 0))
            (r + (SchemeOverField.relativeDimensionGap X Y f : ℤ)))
          (((Scheme.Modules.pullback f.left).obj G).associatedCycle
            (X.hom.relativeDimensionFunction (fun _ ↦ 0))
            (s + (SchemeOverField.relativeDimensionGap X Y f : ℤ)))
          (AlgebraicGeometry.SchemeOverField.pullbackAssociatedCycles_intersectProperly
            X Y f F G r s hF hG hFG))
