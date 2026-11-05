/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure

/-!
# Base change of reduced point closures

This file provides the canonical comparison from the base change of a reduced
point closure to the corresponding base change of the ambient scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PointClosure

/-- The base change of a reduced point closure maps canonically to the base change of its
ambient scheme. -/
def baseChangeMap {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (y : X) :
    pullback g (ι y ≫ f) ⟶ pullback g f :=
  pullback.map g (ι y ≫ f) g f (𝟙 S') (ι y) (𝟙 S)
    ((Category.comp_id g).trans (Category.id_comp g).symm) (Category.comp_id _)

/-- An isomorphism pulls back the reduced closure of its image point to the
reduced closure of the original point. -/
theorem ideal_comap_of_isIso {X Y : Scheme.{u}} (j : Y ⟶ X) [IsIso j] (y : Y) :
    (reducedStructure (j y)).ideal.comap j = (reducedStructure y).ideal := by
  have hcomap (I : X.IdealSheafData) : I.comap j = I.map (inv j) := by
    apply le_antisymm
    · apply IdealSheafData.le_map_iff_comap_le.mpr
      simp only [← IdealSheafData.comap_comp, IsIso.inv_hom_id,
        IdealSheafData.comap_id]
      exact le_rfl
    · have h := IdealSheafData.map_mono (inv j) (I.le_map_comap j)
      simpa only [← IdealSheafData.map_comp, IsIso.hom_inv_id,
        IdealSheafData.map_id] using h
  change (IdealSheafData.vanishingIdeal (closedSubset (j y))).comap j =
    IdealSheafData.vanishingIdeal (closedSubset y)
  rw [hcomap, IdealSheafData.map_vanishingIdeal]
  congr 1
  apply TopologicalSpace.Closeds.ext
  change closure ((inv j) '' closure {j y}) = closure {y}
  rw [← (inv j).isClosedEmbedding.closure_image_eq, Set.image_singleton]
  simp only [← Scheme.Hom.comp_apply, IsIso.hom_inv_id, closure_closure]
  rfl

end AlgebraicGeometry.Scheme.PointClosure
