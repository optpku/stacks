/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Quotient.Module
public import ReasLib.Algebra.Module.ProjectiveFactorIdeal
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.DerivedBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace

@[expose] public section

open CategoryTheory TopologicalSpace
open SheafOfModules.RingedSite SheafOfModules.RingedSite.IdealSheaf
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.IsBlowup

/-- The kernel of the pullback map associated to a short exact complex over a quotient
ring is annihilated by the corresponding power of the pulled-back center ideal. -/
theorem kernelPullback_isAnnihilated
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)]
    {n c : ℕ} (hcn : c ≤ n) (S : ShortComplex (ModuleCat (A ⧸ I ^ n)))
    (hS : S.ShortExact) [Module.Finite (A ⧸ I ^ n) S.X₃]
    (hM : Module.IsIdealProjective
      (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) S.X₃) :
    IsAnnihilated (J := Opens.grothendieckTopology X.toRingedSpace)
      (O := X.toRingedSpace.sheaf)
      (((Scheme.idealSheafDataOfIdealOnSpec I).comap p) ^ c).toSubobject
      (Limits.kernel (toRingedSpaceMap X
        ((affineBaseModuleAssociatedFunctor A p).map
          ((ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).map S.f))) :
        X.toRingedSpace.Modules) := sorry

end AlgebraicGeometry.IsBlowup
