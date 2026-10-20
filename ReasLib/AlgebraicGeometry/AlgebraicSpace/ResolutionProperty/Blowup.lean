/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Admissible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ResolutionProperty

/-!
# Admissible blowups and the resolution property

A quasi-compact quasi-separated algebraic space with finitely many irreducible
components admits an admissible blowup with the resolution property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A quasi-compact quasi-separated algebraic space with finitely many irreducible
components admits a dense quasi-compact open and an admissible blowup over that
open whose source has the resolution property. -/
@[stacks 0GV5]
theorem exists_isAdmissibleBlowup_hasResolutionProperty
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasFiniteIrreducibleComponents X] :
    ∃ (U : OpenSubspace X) (X' : AlgebraicSpace S) (π : X' ⟶ X),
      IsQuasiCompact U.X ∧ Dense U.pointsSet ∧
        IsAdmissibleBlowup U π ∧
          SheafOfModules.HasResolutionProperty (structureSheaf X') :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
