/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle.Presentation

@[expose] public section

open CategoryTheory ComplexShape
open AlgebraicGeometry
open RingedSpace.DeRham.PuncturedLineBundle

noncomputable section

universe u

/- The former source-side support module reexports the reusable presentation API. -/
#check (pushedForwardDeRham :
  ∀ {S X : Scheme.{u}} (f : X ⟶ S) (ℒ : X.Modules)
    [Scheme.Modules.Invertible ℒ]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
    [Scheme.IsRelativeSpectrumOver P],
      CochainComplex (RingedSpace.DeRham.Modules f.toLRSHom.toShHom) ℤ)
