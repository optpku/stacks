/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Shift.Adjunction
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Derived coextension of scalars canonically commutes with integer shifts. -/
noncomputable instance derivedCoextensionOfScalars_commShift (f : R →+* S) :
    (derivedCoextensionOfScalars f).CommShift ℤ :=
  (derivedRestrictionCoextensionAdjunction f).rightAdjointCommShift ℤ

end CategoryTheory.ModuleCat
