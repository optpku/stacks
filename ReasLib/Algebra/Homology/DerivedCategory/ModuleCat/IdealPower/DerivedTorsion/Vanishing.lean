/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.DerivedTorsion
public import ReasLib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.IdealPowerTorsion

variable {A : Type u} [CommRing A]

/-- If an element of a finitely generated ideal acts invertibly on a derived module,
then its derived ideal-power-torsion object is zero. -/
theorem isZero_of_isIso_smul (I : Ideal A) (hI : I.FG) {f : A} (hf : f ∈ I)
    (K : DerivedCategory (ModuleCat A)) [IsIso (f • 𝟙 K)] :
    IsZero ((derivedTorsion I).obj K) := sorry

end CategoryTheory.ModuleCat.IdealPowerTorsion

end
