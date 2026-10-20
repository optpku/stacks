/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.IdealStalk
public import ReasLib.AlgebraicGeometry.Scheme.Module.ClosedImmersion

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

section StalkIdeal

variable {X : Scheme.{u}}

/-- The stalk ideal `𝓘ₓ ⊆ 𝒪_{X, x}` cut out by the ideal sheaf data `D`. -/
abbrev stalkIdeal (D : X.IdealSheafData) (x : X) : Ideal (X.presheaf.stalk x) :=
  RingedSpace.idealSheafStalkIdeal (RingedSpace.Hom.kernelIdealSubobject D.subschemeι.toShHom) x

/-- Identify `stalkIdeal` with the canonical Chapter 20 stalk-ideal owner for the closed
immersion ideal sheaf of `D`. -/
@[simp] theorem stalkIdeal_def (D : X.IdealSheafData) (x : X) :
    D.stalkIdeal x =
      RingedSpace.idealSheafStalkIdeal (RingedSpace.Hom.kernelIdealSubobject D.subschemeι.toShHom) x :=
  rfl

end StalkIdeal

end AlgebraicGeometry.Scheme.IdealSheafData
