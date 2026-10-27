/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import stacks_project.Chap60.Proposition_60_21_1
public import stacks_project.Chap60.Proposition_60_17_4
public import stacks_project.Chap60.Lemma_60_17_3_Functor
public import stacks_project.Chap60.Lemma_60_20_2_Completion
public import ReasLib.AlgebraicGeometry.Crystalline.Completed.DeRham
import StacksCheckRecall

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline
open AlgebraicGeometry.Scheme.Modules
open CompletedCris
open CrystallineModuleSheaf
open CrystallineConnectionPair
open DPPolynomial.DeRham

universe u

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {A : Type u} [CommRing A] {IA : Ideal A} (γA : DividedPowers IA)
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {C : Type u} [CommRing C] [Algebra A C]
variable (hIC : Ideal.map (algebraMap A C) IA = (⊥ : Ideal C))
variable (hpnil : IsNilpotent (p : C))
variable {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
variable (hπ : Function.Surjective π)
variable (J0 : Ideal (MvPolynomial ι A))
variable (hJ0 : J0 = RingHom.ker π.toRingHom)
variable (hIJ0 : Ideal.map (algebraMap A (MvPolynomial ι A)) IA ≤ J0)
variable (E0 : DividedPowerEnvelope IA γA (algebraMap A (MvPolynomial ι A)) J0 hIJ0)
variable (hE0 : DividedPowerEnvelope.IsUniversal γA
  (algebraMap A (MvPolynomial ι A)) hIJ0 E0)
variable (γbar : DividedPowers
  (Ideal.map (algebraMap E0.D
    (crystallineD p IA γA π hπ J0 hJ0 hIC hpnil hIJ0 E0 hE0)) E0.D.ideal))
variable [HasLimits AddCommGrpCat.{u}]

variable (I : (Spec.{u} (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V))
variable (h_compatible :
  ∀ (V : (Spec.{u} (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
    (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen f))
      ((Spec (.of A)).presheaf.map
        (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom)
variable (s : Spec.{u} (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (x₀ : Spec.{u} (.of C) ⟶ I.subscheme)
variable (h_p : ∀ U : (Spec.{u} (.of C)).affineOpens,
  IsNilpotent (p : Γ(Spec (.of C), U)))
variable (hI : specIdealEqOfIdealTop IA I) (hγ : specDividedPowersEq IA γA I γS)
variable (hx₀ : IsCanonicalCrisStructureMap I x₀)
variable (F : CrisModuleSheaf (Spec (.of A)) I γS h_compatible (Spec (.of C)) x₀)
variable [CrisModuleSheaf.IsCrystal F] [ModuleSheaf.IsLocallyQuasiCoherent F]

/- Proposition 60.21.3: the completed de Rham complex of the module with canonical
connection corresponding to a quasi-coherent crystal computes its crystalline
derived global sections in the affine polynomial-envelope setup. -/
@[stacks 07LG] #check
  (CrystallineModuleSheaf.CrisModuleSheaf.Completed.deRhamComplex_computes
    p γA π hπ hJ0 hIC hpnil E0 hE0 I γS h_compatible x₀ (Iso.refl (Spec (.of C)))
    ((Category.id_comp (x₀ ≫ I.subschemeι)).trans hx₀) hI hγ F s h_p :
    IsIsomorphic
      (CrystallineModuleSheaf.derivedGlobalSections p (Spec (.of A)) I γS h_compatible s
        (Spec (.of C)) x₀ h_p F)
      (DerivedCategory.Q.obj
        ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}).obj
          ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex
            (ComplexShape.up ℕ)).obj
              (CrystallineModuleSheaf.CrisModuleSheaf.Completed.deRhamComplex
                p γA π hπ hJ0 hIC hpnil E0 hE0 I γS h_compatible x₀
                (Iso.refl (Spec (.of C)))
                ((Category.id_comp (x₀ ≫ I.subschemeι)).trans hx₀) hI hγ F)))))

variable (n : ℕ)

#check
  (CrystallineModuleSheaf.CrisModuleSheaf.Completed.deRhamComplex_cohomology
    p γA π hπ hJ0 hIC hpnil E0 hE0 I γS h_compatible x₀ (Iso.refl (Spec (.of C)))
    ((Category.id_comp (x₀ ≫ I.subschemeι)).trans hx₀) hI hγ F s h_p n :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (n : ℤ)).obj
        (CrystallineModuleSheaf.derivedGlobalSections p (Spec (.of A)) I γS h_compatible s
          (Spec (.of C)) x₀ h_p F))
      (((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (CrystallineModuleSheaf.CrisModuleSheaf.Completed.deRhamComplex
            p γA π hπ hJ0 hIC hpnil E0 hE0 I γS h_compatible x₀
            (Iso.refl (Spec (.of C)))
            ((Category.id_comp (x₀ ≫ I.subschemeι)).trans hx₀) hI hγ F)).homology n))

end
