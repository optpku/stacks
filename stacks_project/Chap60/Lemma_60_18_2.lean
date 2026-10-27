/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Crystalline.Module.Sections


open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline
open AlgebraicGeometry.Scheme.Modules
open CrystallineModuleSheaf

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (S : Scheme.{u}) (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/- Lemma 60.18.2 -/
@[stacks 07JK]
#check (AlgebraicGeometry.Scheme.Crystalline.locallyQuasiCoherent_derivedGlobalSections_iso_chaotic
    p S I γ h_compatible s X x₀ h_p : ∀ [IsAffine X] [IsAffine S]
    (h_I_quasiCoherent : I.toModule.IsQuasicoherent)
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [ModuleSheaf.IsLocallyQuasiCoherent F]
    (hF : IsCrisSheaf p s h_p F),
    IsIsomorphic
      ((siteAbelianGlobalSectionsDerived (chaoticTopology S I γ h_compatible X x₀)).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (chaoticTopology S I γ h_compatible X x₀) AddCommGrpCat.{u + 1}) 0).obj
          (restrictToChaotic p S I γ h_compatible s X x₀ h_p
            (hF.abelianSheafULift p s h_p))))
      ((siteAbelianGlobalSectionsDerived
          (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (smallCrystallineTopology p S I γ h_compatible s X x₀ h_p)
              AddCommGrpCat.{u + 1}) 0).obj
          (hF.abelianSheafULift p s h_p))))

end AlgebraicGeometry.Scheme.Crystalline

end
