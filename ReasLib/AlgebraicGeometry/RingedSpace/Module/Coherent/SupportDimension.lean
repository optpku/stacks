/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support

/-!
# Coherent sheaves with bounded support dimension

This file defines the object property of coherent sheaves whose support is bounded with respect
to an integer-valued function, together with its canonical full-subcategory view.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace.Coh

/-- Coherent module sheaves whose support lies in the locus where `d ≤ k`. -/
def supportDimensionLE {X : RingedSpace.{u}} (d : X → ℤ) (k : ℤ) :
    ObjectProperty (RingedSpace.Coh X) :=
  (RingedSpace.moduleSupportedOn {x | d x ≤ k}).inverseImage
    (SheafOfModules.isCoherent X.ringCatSheaf).ι

/-- Membership in `supportDimensionLE d k` is the pointwise bound on the module support. -/
theorem supportDimensionLE_iff {X : RingedSpace.{u}} (d : X → ℤ) (k : ℤ)
    (F : RingedSpace.Coh X) :
    supportDimensionLE d k F ↔ ∀ x ∈ RingedSpace.moduleSupport F.obj, d x ≤ k := sorry

end AlgebraicGeometry.RingedSpace.Coh

namespace AlgebraicGeometry.RingedSpace

/-- The full subcategory of coherent module sheaves whose `d`-support dimension is at most `k`. -/
abbrev CohLE (X : RingedSpace.{u}) (d : X → ℤ) (k : ℤ) :=
  (Coh.supportDimensionLE d k).FullSubcategory

namespace CohLE

/-- Every support point of an object of `CohLE X d k` has `d`-value at most `k`. -/
theorem support_le {X : RingedSpace.{u}} {d : X → ℤ} {k : ℤ} (F : CohLE X d k)
    {x : X} (hx : x ∈ RingedSpace.moduleSupport F.obj.obj) : d x ≤ k := sorry

end CohLE

end AlgebraicGeometry.RingedSpace
