/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Action
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InvertiblePower.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Successive quotients of powers of an invertible ideal sheaf

An invertible ideal subsheaf has integral tensor powers.  Multiplication by the ideal gives the
successor inclusions, and their cokernels form canonical short exact rows relating two successive
graded pieces.  This file owns that algebraic input independently of eta complexes, derived
categories, and Bockstein operators.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite.IdealSheaf

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IdealSheaf.Power

variable {X : RingedSpace.{u}}

/-- Multiplication gives the canonical inclusion `I^⊗(i + 1) ⟶ I^⊗i`. -/
noncomputable def succ
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)] (i : ℤ) :
    (I : X.Modules) ^⊗ (i + 1) ⟶ (I : X.Modules) ^⊗ i :=
  (RingedSpace.InvertiblePower.oneAddIso (I : X.Modules) i).symm.hom ≫
    action I ((I : X.Modules) ^⊗ i)

/-- The inclusion of ideal powers separated by two degrees. -/
noncomputable def twoStep
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)] (i : ℤ) :
    (I : X.Modules) ^⊗ (i + 1 + 1) ⟶ (I : X.Modules) ^⊗ i :=
  succ I (i + 1) ≫ succ I i

/-- The successive graded piece `I^⊗i / I^⊗(i + 1)`. -/
@[stacks 0GT8 "successive quotient of invertible ideal powers"]
noncomputable abbrev piece
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)] (i : ℤ) : X.Modules :=
  cokernel (succ I i)

/-- The two-step quotient `I^⊗i / I^⊗(i + 2)`. -/
noncomputable abbrev twoStepPiece
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)] (i : ℤ) : X.Modules :=
  cokernel (twoStep I i)

/-- The successor inclusion vanishes in the two-step quotient after one further multiplication. -/
theorem inclusion_w
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)] (i : ℤ) :
    succ I (i + 1) ≫ succ I i ≫ cokernel.π (twoStep I i) = 0 := sorry

/-- The canonical inclusion of the next graded piece into the two-step quotient. -/
noncomputable def inclusion
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)] (i : ℤ) :
    piece I (i + 1) ⟶ twoStepPiece I i :=
  cokernel.desc (succ I (i + 1))
    (succ I i ≫ cokernel.π (twoStep I i)) (inclusion_w I i)

/-- The two-step inclusion vanishes after projection to the first graded piece. -/
theorem projection_w
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)] (i : ℤ) :
    twoStep I i ≫ cokernel.π (succ I i) = 0 := sorry

/-- The canonical projection from the two-step quotient to the current graded piece. -/
noncomputable def projection
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)] (i : ℤ) :
    twoStepPiece I i ⟶ piece I i :=
  cokernel.desc (twoStep I i) (cokernel.π (succ I i)) (projection_w I i)

/-- The inclusion and projection of the ideal-power quotient row compose to zero. -/
theorem inclusion_comp_projection
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)] (i : ℤ) :
    inclusion I i ≫ projection I i = 0 := sorry

/-- The canonical row
`I^(i + 1) / I^(i + 2) ⟶ I^i / I^(i + 2) ⟶ I^i / I^(i + 1)`. -/
@[stacks 0GT8 "successive ideal-power quotient row"]
noncomputable def row
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)] (i : ℤ) :
    ShortComplex X.Modules :=
  ShortComplex.mk (inclusion I i) (projection I i)
    (inclusion_comp_projection I i)

/-- The canonical row of successive quotients of powers of an invertible ideal is short exact. -/
@[stacks 0GT8 "short exact successive ideal-power quotient row"]
theorem row_shortExact
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    [isInvertibleObject (I : X.Modules)] (i : ℤ) :
    (row I i).ShortExact := sorry

end AlgebraicGeometry.RingedSpace.IdealSheaf.Power
