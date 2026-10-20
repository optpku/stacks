/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent.SupportDimension

open CategoryTheory

universe u

section

variable (X : AlgebraicGeometry.RingedSpace.{u}) (d : X → ℤ) (k : ℤ)

/- The bounded-support object property is provided by the reusable support-dimension owner. -/
#check (AlgebraicGeometry.RingedSpace.Coh.supportDimensionLE d k :
  ObjectProperty (AlgebraicGeometry.RingedSpace.Coh X))

/- Its membership theorem identifies bounded support pointwise. -/
#check (AlgebraicGeometry.RingedSpace.Coh.supportDimensionLE_iff d k :
  ∀ F : AlgebraicGeometry.RingedSpace.Coh X,
    AlgebraicGeometry.RingedSpace.Coh.supportDimensionLE d k F ↔
      ∀ x ∈ AlgebraicGeometry.RingedSpace.moduleSupport F.obj, d x ≤ k)

/- The bounded-support full subcategory is reusable independently of its Serre property. -/
#check (AlgebraicGeometry.RingedSpace.CohLE X d k : Type (u + 1))

variable (F : AlgebraicGeometry.RingedSpace.CohLE X d k)

/- Objects of the bounded-support full subcategory satisfy the pointwise support bound. -/
#check (AlgebraicGeometry.RingedSpace.CohLE.support_le F :
  ∀ {x : X}, x ∈ AlgebraicGeometry.RingedSpace.moduleSupport F.obj.obj → d x ≤ k)

end
