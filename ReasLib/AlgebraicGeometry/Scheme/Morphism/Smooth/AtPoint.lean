/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic

/-!
# Smooth morphisms at a point

This module gives affine-neighborhood and smooth-locus criteria for a scheme
morphism to be smooth at a point.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Given an affine neighborhood `V` of `f x`, a morphism is smooth at `x`
exactly when some affine neighborhood of `x` restricts to a standard smooth
morphism over `V`. -/
theorem smoothAt_iff_exists_standardSmooth_affineChart_over
    (x : X) (V : S.affineOpens) (hxV : f x ∈ (V : S.Opens)) :
    f.SmoothAt x ↔
      ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ e : U ≤ f ⁻¹ᵁ V,
          StandardSmooth (f.resLE V U e) := sorry

/-- For a locally finitely presented morphism, smoothness at a point is
equivalent to membership in its smooth locus. -/
theorem smoothAt_iff_mem_smoothLocus [LocallyOfFinitePresentation f] (x : X) :
    f.SmoothAt x ↔ x ∈ f.smoothLocus := sorry

/-- Given an affine neighborhood `V` of `f x`, a point belongs to the smooth
locus exactly when some affine neighborhood of it restricts to a standard
smooth morphism over `V`. -/
theorem mem_smoothLocus_iff_exists_standardSmooth_affineChart_over
    [LocallyOfFinitePresentation f]
    (x : X) (V : S.affineOpens) (hxV : f x ∈ (V : S.Opens)) :
    x ∈ f.smoothLocus ↔
      ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ e : U ≤ f ⁻¹ᵁ V,
          StandardSmooth (f.resLE V U e) := by
  rw [← f.smoothAt_iff_mem_smoothLocus x]
  exact f.smoothAt_iff_exists_standardSmooth_affineChart_over x V hxV

end AlgebraicGeometry.Scheme.Hom
