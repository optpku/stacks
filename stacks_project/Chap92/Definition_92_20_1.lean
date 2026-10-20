/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.CotangentComplex
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 92.20.1: Let `f : (X, O_X) ⟶ (S, O_S)` be a morphism of ringed
spaces. The cotangent complex `L_f` of `f` is `L_f = L_{O_X / f⁻¹ O_S}`. We will
also use the notation `L_f = L_{X/S} = L_{O_X / O_S}`. -/
@[stacks 08UU]
#check (AlgebraicGeometry.RingedSpace.cotangentComplex :
  ∀ {X S : AlgebraicGeometry.RingedSpace.{u}},
    (X ⟶ S) → CochainComplex X.Modules ℤ)
