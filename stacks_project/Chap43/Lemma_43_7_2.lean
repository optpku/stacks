/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.Composition.Variety

open AlgebraicGeometry CategoryTheory

universe u

section

variable {K : Type u} [Field K]
variable (X Y Z : SchemeOverField K) [Variety X] [Variety Y] [Variety Z]
variable (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f.left] [Flat g.left]
variable (k : ℤ)

/- Lemma 43.7.2 (1): the composite of flat morphisms of varieties is flat. -/
@[stacks 0B0P] #check
  (AlgebraicGeometry.Flat.overComp f g : Flat (f ≫ g).left)

/- Lemma 43.7.2 (2): successive graded flat pullbacks agree, after degree
reindexing, with flat pullback along the composite. -/
@[stacks 0B0P] #check
  (AlgebraicGeometry.CycleGroup.flatPullback_comp_of_varieties X Y Z f g k :
    (AlgebraicGeometry.CycleGroup.reindex
      (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0))
      (AlgebraicGeometry.CycleGroup.flatPullback_comp_variety_source_degree
        X Y Z f g k)).comp
        ((AlgebraicGeometry.CycleGroup.flatPullback
          (fun _ : Spec (CommRingCat.of K) ↦ 0) X Y f
          (SchemeOverField.relativeDimensionGap X Y f)
          (k + (SchemeOverField.relativeDimensionGap Y Z g : ℤ))).comp
          (AlgebraicGeometry.CycleGroup.flatPullback
            (fun _ : Spec (CommRingCat.of K) ↦ 0) Y Z g
            (SchemeOverField.relativeDimensionGap Y Z g) k)) =
      (AlgebraicGeometry.CycleGroup.reindex
        (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0))
        (AlgebraicGeometry.CycleGroup.flatPullback_comp_variety_composite_degree
          X Y Z f g k)).comp
          (AlgebraicGeometry.CycleGroup.flatPullback
            (fun _ : Spec (CommRingCat.of K) ↦ 0) X Z (f ≫ g)
            (SchemeOverField.relativeDimensionGap X Y f +
              SchemeOverField.relativeDimensionGap Y Z g) k))

end
