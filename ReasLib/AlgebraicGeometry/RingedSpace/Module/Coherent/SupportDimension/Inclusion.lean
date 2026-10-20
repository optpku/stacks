/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent.SupportDimension

/-!
# Inclusions between coherent support bounds

This file constructs the canonical inclusion between full subcategories of coherent sheaves
whose support dimensions satisfy ordered bounds.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace.Coh

/-- The coherent support-dimension object property is monotone in its integer bound. -/
theorem supportDimensionLE_mono {X : RingedSpace.{u}} {d : X → ℤ} {a b : ℤ} (h : a ≤ b) :
    supportDimensionLE d a ≤ supportDimensionLE d b := sorry

end AlgebraicGeometry.RingedSpace.Coh

namespace AlgebraicGeometry.RingedSpace.CohLE

/-- The canonical inclusion from coherent sheaves supported in dimension at most `a` to those
supported in dimension at most `b`, when `a ≤ b`. -/
def inclusion {X : RingedSpace.{u}} {d : X → ℤ} {a b : ℤ} (h : a ≤ b) :
    CohLE X d a ⥤ CohLE X d b :=
  ObjectProperty.ιOfLE (Coh.supportDimensionLE_mono h)

/-- Changing a coherent support bound leaves the underlying coherent sheaf unchanged. -/
theorem inclusion_obj {X : RingedSpace.{u}} {d : X → ℤ} {a b : ℤ} (h : a ≤ b)
    (F : CohLE X d a) : ((inclusion h).obj F).obj = F.obj := sorry

end AlgebraicGeometry.RingedSpace.CohLE
