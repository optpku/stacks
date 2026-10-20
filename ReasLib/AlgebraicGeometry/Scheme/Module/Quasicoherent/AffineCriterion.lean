/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Equivalence

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/-- A quasi-compact and quasi-separated scheme is affine if its category of
quasicoherent modules is equivalent to modules over a commutative ring. -/
theorem isAffine_of_moduleEquivalence
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (h_equiv : ∃ (R : Type u) (_ : CommRing R),
      Nonempty (Scheme.QCoh X ≌ ModuleCat.{u} R)) : IsAffine X := sorry

end AlgebraicGeometry.Scheme.QCoh
