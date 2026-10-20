/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.OpenComplement
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The annihilation of structure-sheaf cohomology on an affine complement by a
power of an ideal transfers to every finite locally free module sheaf. -/
@[stacks 0BM5]
theorem cohomology_isAnnihilatedByPower_of_finiteLocallyFree
    {A : Type u} [CommRing A] (J I : Ideal A) (hJI : J ≤ I) (hJ : J.FG) (hI : I.FG)
    (p : ℕ) :
    let U := (Scheme.idealSheafDataOfIdealOnSpec I).openComplement
    let JU := Ideal.map
      (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ U.ι.appTop).hom) J
    Module.IsAnnihilatedByPower JU
        (cohomology (SheafOfModules.unit U.toScheme.ringCatSheaf : U.toScheme.Modules) p) →
      ∀ (F : U.toScheme.Modules) [F.IsFiniteLocallyFree],
        Module.IsAnnihilatedByPower JU (cohomology F p) := sorry

end AlgebraicGeometry.Scheme.Modules
