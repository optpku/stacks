/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.PPowerLimit

open AlgebraicGeometry CategoryTheory Opposite CrystallineModuleSheaf
open AlgebraicGeometry.Scheme.Crystalline
open AlgebraicGeometry.Scheme.Crystalline.PPower

universe u

/- Remark 60.24.10 (Rlim): crystalline cohomology of any module sheaf is the derived
inverse limit of its restrictions to the sufficiently large prime-power quotient bases. -/
@[stacks 07MV] #check (AlgebraicGeometry.Scheme.Crystalline.PPower.cohomologyRlim :
  ∀ (p : ℕ) [Fact (Nat.Prime p)] {A : Type u} [CommRing A]
    [Algebra (Int.LocalizationAtPrime p) A]
    (I : (Spec (.of A)).IdealSheafData)
    (γ : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (I.ideal V))
    (h_compatible : ∀ (V : (Spec (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
      (γ V).IsDPMorphism (γ ((Spec (.of A)).affineBasicOpen f))
        ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (h_I_quasiCoherent : I.toModule.IsQuasicoherent)
    (h_pAmodI : IsNilpotent (Ideal.Quotient.mk
      (I.ideal ⟨⊤, isAffineOpen_top (Spec (.of A))⟩) (p : Γ(Spec (.of A), ⊤))))
    (F : CrisModuleSheaf (Spec (.of A)) I γ h_compatible X x₀)
    (hF : CrystallineModuleSheaf.IsCrisSheaf p (baseMap A p) h_p F)
    (e₀ : ℕ) (h_tail : StableTail p I γ e₀),
    HomotopyLimit.IsOf
      (rGammaSystem p I γ h_compatible X x₀ h_p (hF.abelianSheafULift p (baseMap A p) h_p) e₀)
      ((siteAbelianGlobalSectionsDerived
        (smallCrystallineTopology p (Spec (.of A)) I γ h_compatible (baseMap A p) X x₀ h_p)).obj
          ((DerivedCategory.singleFunctor
            (Sheaf (smallCrystallineTopology p (Spec (.of A)) I γ h_compatible
              (baseMap A p) X x₀ h_p) AddCommGrpCat.{u + 1}) 0).obj
                (hF.abelianSheafULift p (baseMap A p) h_p))))
