/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.PowerQuotient.Module
public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite.IdealSheaf

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {Y : RingedSpace.{u}}

/-- The conormal module `I / I ^ 2` of an ideal sheaf `I` on a ringed space. -/
noncomputable abbrev conormalModule (I : IdealSubobject Y) : Y.Modules :=
  PowerQuotientModule.stage.{u, u, u} I I.toModule 1

/-- The structure module `𝒪_Y / I ^ 2` of the second-order thickening. -/
noncomputable abbrev secondOrderStructureModule (I : IdealSubobject Y) : Y.Modules :=
  PowerQuotientModule.stage.{u, u, u} I (SheafOfModules.unit Y.ringCatSheaf) 2

/-- The quotient structure module `𝒪_Y / I`. -/
noncomputable abbrev quotientStructureModule (I : IdealSubobject Y) : Y.Modules :=
  PowerQuotientModule.stage.{u, u, u} I (SheafOfModules.unit Y.ringCatSheaf) 1

/-- Multiplication by `I` on itself becomes zero after inclusion into `𝒪_Y` and projection
to `𝒪_Y / I ^ 2`. -/
theorem conormalInclusion_condition (I : IdealSubobject Y) :
    powerAction.{u, u, u} I I.toModule 1 ≫
      I.arrow ≫ PowerQuotientModule.projection.{u, u, u} I
        (SheafOfModules.unit Y.ringCatSheaf) 2 = 0 := sorry

/-- The canonical inclusion `I / I ^ 2 ⟶ 𝒪_Y / I ^ 2`. -/
noncomputable def conormalInclusion (I : IdealSubobject Y) :
    conormalModule I ⟶ secondOrderStructureModule I :=
  cokernel.desc (powerAction.{u, u, u} I I.toModule 1)
    (I.arrow ≫ PowerQuotientModule.projection.{u, u, u} I
      (SheafOfModules.unit Y.ringCatSheaf) 2)
    (conormalInclusion_condition I)

/-- The canonical projection `𝒪_Y / I ^ 2 ⟶ 𝒪_Y / I`. -/
noncomputable abbrev secondOrderProjection (I : IdealSubobject Y) :
    secondOrderStructureModule I ⟶ quotientStructureModule I :=
  PowerQuotientModule.step.{u, u, u} I (SheafOfModules.unit Y.ringCatSheaf) 1

/-- The conormal inclusion followed by the quotient projection is zero. -/
theorem conormalInclusion_comp_secondOrderProjection (I : IdealSubobject Y) :
    conormalInclusion I ≫ secondOrderProjection I = 0 := sorry

/-- The canonical row `I / I ^ 2 ⟶ 𝒪_Y / I ^ 2 ⟶ 𝒪_Y / I`. -/
noncomputable def secondOrderThickeningRow (I : IdealSubobject Y) : ShortComplex Y.Modules :=
  ShortComplex.mk (conormalInclusion I) (secondOrderProjection I)
    (conormalInclusion_comp_secondOrderProjection I)

/-- The canonical sequence
`0 ⟶ I / I ^ 2 ⟶ 𝒪_Y / I ^ 2 ⟶ 𝒪_Y / I ⟶ 0` is exact. -/
theorem secondOrderThickeningRow_shortExact (I : IdealSubobject Y) :
    (secondOrderThickeningRow I).ShortExact := sorry

end AlgebraicGeometry.RingedSpace
