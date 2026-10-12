/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
