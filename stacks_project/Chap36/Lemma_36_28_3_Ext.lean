/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ProjectionFormula.Ext

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.DerivedCategory

noncomputable section

universe u

/- This compatibility bridge preserves the historical import surface for the
integer-graded quasicoherent cohomology API. -/
#check
  (AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula.qcCohomology :
    ∀ {S : Scheme.{u}},
      DeltaFunctor S.Modules (DerivedCategory AddCommGrpCat.{u}) → ℤ →
        Scheme.QCoh S ⥤ AddCommGrpCat.{u})
