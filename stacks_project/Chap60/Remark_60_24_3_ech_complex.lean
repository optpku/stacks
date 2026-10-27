/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Cech.Comparison
import StacksCheckRecall


@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline
open AlgebraicGeometry.Scheme.Modules
open CrystallineModuleSheaf
open CechCrisCover
open CechCrisEnvelope

universe u

variable (p : ℕ) [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable (IA : Ideal A) (γA : DividedPowers IA)
variable {I : (Spec.{u} (.of A)).IdealSheafData}
variable {γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible :
    ∀ (V : (Spec.{u} (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
      (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen f))
        ((Spec (.of A)).presheaf.map
          (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
variable (c : CechCrisCover x₀)
variable (s : Spec.{u} (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (E : CechCrisEnvelope p IA γA c)

/- Remark 60.24.3 (Čech complex) (1) -/
@[stacks 07MM] #check (CechCrisEnvelope.computes p IA γA c s h_p E :
  ∀ (hI : Affine.idealCompatible IA I)
    (hγ : Affine.dividedPowersCompatible IA γA I γS)
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible X x₀)
    [ModuleSheaf.IsLocallyQuasiCoherent F]
    [CrisModuleSheaf.IsCrystal F],
    IsIsomorphic
      (derivedGlobalSections p (Spec (.of A)) I γS h_compatible s X x₀ h_p F)
      ((DerivedCategory.Q).obj
        ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}).obj
          ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex
            (ComplexShape.up ℕ)).obj (E.cechCrisComplex s h_p hI hγ F)))))


/- Remark 60.24.3 (Čech complex) (2) -/
@[stacks 07MM] #check (CechCrisEnvelope.computes_of_epi p IA γA c s h_p E :
  ∀ (hI : Affine.idealCompatible IA I)
    (hγ : Affine.dividedPowersCompatible IA γA I γS)
    (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible X x₀)
    [ModuleSheaf.IsLocallyQuasiCoherent F]
    (hF : IsCrisSheaf p s h_p F)
    (h_epi : AlgebraicGeometry.Scheme.Crystalline.comparison_epi_of_closedImmersion
      (Spec (.of A)) I γS h_compatible X x₀ F),
    IsIsomorphic
      (derivedGlobalSections p (Spec (.of A)) I γS h_compatible s X x₀ h_p F)
      ((DerivedCategory.Q).obj
        ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}).obj
          ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex
            (ComplexShape.up ℕ)).obj (E.cechCrisComplex s h_p hI hγ F)))))

end
