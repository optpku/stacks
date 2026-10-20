/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AlmostBlowup
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject

/-!
# Existence of almost blowup squares

Finite-type quasi-coherent ideal sheaves on quasi-compact and quasi-separated schemes occur as
the centers of almost blowup squares.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A finite-type quasi-coherent ideal sheaf on a quasi-compact and quasi-separated scheme is the
center of an almost blowup square. -/
theorem exists_isAlmostBlowupSquare {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (I : X.IdealSheafData) [I.toModule.IsQuasicoherent]
    (hI : I.IsFiniteType) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X), IsAlmostBlowupSquare b I := sorry

end AlgebraicGeometry
