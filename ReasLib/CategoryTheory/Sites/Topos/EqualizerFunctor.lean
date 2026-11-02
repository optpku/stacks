/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Pointwise equalizer functors

The equalizer of two natural transformations is assembled from the chosen
equalizers in the target category. Its objects and inclusion components are
definitionally the corresponding Mathlib equalizers, so it can be used without
changing objectwise presentations of direct images.
-/

@[expose] public section

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {source target : C ⥤ D} (left right : source ⟶ target)
variable [∀ object, HasEqualizer (left.app object) (right.app object)]

/-- Assemble the chosen objectwise equalizers of two natural transformations. -/
noncomputable def pointwiseEqualizer : C ⥤ D where
  obj object := equalizer (left.app object) (right.app object)
  map {object other} arrow :=
    equalizer.lift (equalizer.ι (left.app object) (right.app object) ≫ source.map arrow)
      (by
        rw [Category.assoc, left.naturality, ← Category.assoc,
          equalizer.condition, Category.assoc, ← right.naturality, ← Category.assoc])
  map_id := by
    intro object
    apply equalizer.hom_ext
    simp only [equalizer.lift_ι, source.map_id, Category.comp_id, Category.id_comp]
  map_comp := by
    intro object other third arrow next
    apply equalizer.hom_ext
    simp only [equalizer.lift_ι, source.map_comp, Category.assoc]
    simp only [← Category.assoc, equalizer.lift_ι]

/-- The assembled functor retains the chosen objectwise equalizers. -/
theorem pointwiseEqualizer_obj (object : C) :
    (pointwiseEqualizer left right).obj object =
      equalizer (left.app object) (right.app object) := rfl

/-- The induced map is determined by the source functor and the equalizer inclusion. -/
@[reassoc (attr := simp)]
theorem pointwiseEqualizer_map_ι {object other : C} (arrow : object ⟶ other) :
    (pointwiseEqualizer left right).map arrow ≫
        equalizer.ι (left.app other) (right.app other) =
      equalizer.ι (left.app object) (right.app object) ≫ source.map arrow :=
  equalizer.lift_ι _ _

/-- The natural inclusion of the objectwise equalizers into the source functor. -/
noncomputable def pointwiseEqualizerι : pointwiseEqualizer left right ⟶ source where
  app object := equalizer.ι (left.app object) (right.app object)
  naturality _ _ arrow := pointwiseEqualizer_map_ι left right arrow

/-- The fork in the functor category formed by the pointwise equalizers. -/
noncomputable def pointwiseEqualizerFork : Fork left right :=
  Fork.ofι (pointwiseEqualizerι left right) (by
    ext object
    exact equalizer.condition _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The pointwise fork is an equalizer in the functor category. -/
noncomputable def pointwiseEqualizerForkIsLimit :
    IsLimit (pointwiseEqualizerFork left right) :=
  Fork.IsLimit.mk _
    (fun fork ↦
      { app := fun object ↦ equalizer.lift (fork.ι.app object) (congr_app fork.condition object)
        naturality := by
          intro object other arrow
          apply equalizer.hom_ext
          change (fork.pt.map arrow ≫
              equalizer.lift (fork.ι.app other) (congr_app fork.condition other)) ≫
                equalizer.ι (left.app other) (right.app other) =
            (equalizer.lift (fork.ι.app object) (congr_app fork.condition object) ≫
              (pointwiseEqualizer left right).map arrow) ≫
                equalizer.ι (left.app other) (right.app other)
          calc
            _ = fork.pt.map arrow ≫ fork.ι.app other := by
              rw [Category.assoc, equalizer.lift_ι]
            _ = fork.ι.app object ≫ source.map arrow := fork.ι.naturality arrow
            _ = _ := by
              rw [Category.assoc, pointwiseEqualizer_map_ι, ← Category.assoc,
                equalizer.lift_ι] })
    (by
      intro fork
      ext object
      change equalizer.lift (fork.ι.app object) (congr_app fork.condition object) ≫
        equalizer.ι (left.app object) (right.app object) = _
      exact equalizer.lift_ι _ _)
    (by
      intro fork lift condition
      ext object
      apply equalizer.hom_ext
      change lift.app object ≫ equalizer.ι (left.app object) (right.app object) =
        equalizer.lift (fork.ι.app object) (congr_app fork.condition object) ≫
          equalizer.ι (left.app object) (right.app object)
      rw [equalizer.lift_ι]
      exact congr_app condition object)

end CategoryTheory.Limits
