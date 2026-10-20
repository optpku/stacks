/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.Wedge
import StacksCheckRecall

open CategoryTheory

universe u

variable {X S : AlgebraicGeometry.RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat]

/- 50.4.0.1: The exterior products on relative differential forms assemble into the canonical
morphism `Tot(Ωᵈᴿ[X/S] ⊗ Ωᵈᴿ[X/S]) ⟶ Ωᵈᴿ[X/S]`. -/
@[stacks 0FM2] #check (AlgebraicGeometry.RingedSpace.DeRham.wedge :
  (f : X ⟶ S) →
    HomologicalComplex.tensorObj
      (AlgebraicGeometry.RingedSpace.DeRham.complex f)
      (AlgebraicGeometry.RingedSpace.DeRham.complex f) ⟶
    AlgebraicGeometry.RingedSpace.DeRham.complex f)
