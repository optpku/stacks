/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.DeRhamRestriction

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline CrystallineModuleSheaf
open scoped AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {I : S.IdealSheafData}
    {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    (p : ℕ) [Fact (Nat.Prime p)]
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [F.IsCrystal] [F.IsLocallyQuasiCoherent]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    [HasSheafify (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      AddCommGrpCat.{u}]
    [HasSheafify (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
      AddCommGrpCat.{u + 1}]
    [HasSheafify (Opens.grothendieckTopology T.obj.1.thickening) AddCommGrpCat.{u + 1}]

/- 60.23.2.1 -/
@[stacks 07LP] #check
  (AlgebraicGeometry.Scheme.Crystalline.crystallineRestrictionComplex p s h_p F T :
    IsIso (crystallineDeRhamComparison p s h_p F) →
    IsIso (crystallineDeRhamLocalComparisonDerived p s h_p F T) →
    ((siteAbelianGlobalSectionsDerived
      (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)).obj
        (crystalCoefficientDerived p s h_p F) ⟶
    (siteAbelianGlobalSectionsDerived.{u, u, u + 1, u + 1}
      (Opens.grothendieckTopology T.obj.1.thickening)).obj (crystalDeRhamOnTDerived F T)))

