/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Family.EffectiveCartier

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules.AmpleFamily

/-- A quasi-compact, quasi-separated scheme with finitely many irreducible components admits
a quasi-compact dense open and an admissible blowup carrying an ample family of invertible
modules. -/
theorem exists_admissibleBlowup {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [Finite (irreducibleComponents X)] :
    ∃ (U : X.Opens) (X' : Scheme.{u}) (b : X' ⟶ X),
      QuasiCompact U.ι ∧ Dense (U : Set X) ∧ IsAdmissibleBlowup U b ∧
        ∃ (ι : Type u) (L : ι → X'.Modules), AmpleFamily L := sorry

end AlgebraicGeometry.Scheme.Modules.AmpleFamily
