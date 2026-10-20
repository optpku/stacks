/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Flattening.InDimensions

open CategoryTheory

noncomputable section

universe u

open AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) (n : ℕ)
variable [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]

#check
  (AlgebraicGeometry.Scheme.Modules.flatOverInDimensionsGE ℱ f n : Prop)

#check
  (AlgebraicGeometry.Scheme.Flattening.flatInDimensionsFunctor f ℱ n :
    (Over S)ᵒᵖ ⥤ Type u)
