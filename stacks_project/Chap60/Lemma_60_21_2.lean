/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Crystalline.Affine.Cohomology
public import ReasLib.AlgebraicGeometry.Crystalline.Cech.Polynomial
public import ReasLib.AlgebraicGeometry.Crystalline.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Crystalline.Module.Underlined
public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.Restriction

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf

universe u

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] {IA : Ideal A} (γA : DividedPowers IA)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {C : Type u} [CommRing C] [Algebra A C]
variable (hIC : Ideal.map (algebraMap A C) IA = (⊥ : Ideal C))
variable (hpnil : IsNilpotent (p : C))

/- Lemma 60.21.2 -/
@[stacks 07LF]
#check (AlgebraicGeometry.Scheme.Crystalline.Affine.tensorOmegaPower_cohomology_isZero γA hIC hpnil : ∀ (I : (Spec.{u} (.of A)).IdealSheafData)
    (γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : (Spec.{u} (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
        (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen f))
          ((Spec (.of A)).presheaf.map
            (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom)
    (s : Spec.{u} (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (x₀ : Spec.{u} (.of C) ⟶ I.subscheme)
    (h_p : ∀ U : (Spec.{u} (.of C)).affineOpens,
      IsNilpotent (p : Γ(Spec (.of C), U)))
    (hI : Affine.idealCompatible IA I)
    (hγ : Affine.dividedPowersCompatible IA γA I γS)
    (hx₀ : Affine.structureMapCompatible I x₀)
    (h_I_quasiCoherent : I.toModule.IsQuasicoherent)
    [HasSheafify
      (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
        (Spec (.of C)) x₀ h_p)
      AddCommGrpCat.{u}]
    [HasExt (Sheaf (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
      (Spec (.of C)) x₀ h_p) AddCommGrpCat.{u})]
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)
    (hF : IsCrisSheaf p s h_p F)
    [ModuleSheaf.IsLocallyQuasiCoherent F]
    (h_epi : comparison_epi_of_closedImmersion (Spec (.of A)) I γS h_compatible
      (Spec (.of C)) x₀ F)
    (Ω : CrystallineDifferentials p (Spec (.of A)) I γS h_compatible
      h_I_quasiCoherent s (Spec (.of C)) x₀ h_p)
    (i j : ℕ) (hi : 0 < i),
    IsZero
      ((Sheaf.functorH
          (smallCrystallineTopology p (Spec (.of A)) I γS h_compatible s
            (Spec (.of C)) x₀ h_p) j).obj
        (crystallineTensorOmegaPowerSheaf p s h_p F hF Ω i)))

end
