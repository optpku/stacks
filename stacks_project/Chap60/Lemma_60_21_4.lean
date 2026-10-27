/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Completed.Smooth.DeRham
import StacksCheckRecall

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
open DividedPowerEnvelope CrystallineModuleSheaf
open CrystallineModuleSheaf.CrisModuleSheaf.Completed

universe u

variable {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable (I : Ideal A) (γ : DividedPowers I)
variable {C : Type u} [CommRing C] [Algebra A C]
variable {P' : Type u} [CommRing P'] [Algebra A P']
variable (π' : P' →ₐ[A] C)
variable (hπ' : Function.Surjective π')
variable (J' : Ideal P')
variable (hJ' : J' = RingHom.ker π'.toRingHom)
variable (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
variable (hpnil : IsNilpotent (p : C))
variable (hIJ' : Ideal.map (algebraMap A P') I ≤ J')
variable (E' : DividedPowerEnvelope I γ (algebraMap A P') J' hIJ')
variable (hE' : DividedPowerEnvelope.IsUniversal γ (algebraMap A P') hIJ' E')

variable [Algebra.Smooth A P']
variable (R : PolynomialRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')


variable (IS : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (IS.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen f))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom)
variable (x₀ : Spec (.of C) ⟶ IS.subscheme)
variable (hI : Affine.idealCompatible I IS)
variable (hγ : Affine.dividedPowersCompatible I γ IS γS)
variable (hx₀ : Affine.structureMapCompatible IS x₀)
variable (F : quasiCoherentCrystals IS γS hc x₀)

variable (s : Spec (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (h_p : ∀ U : (Spec (.of C)).affineOpens, IsNilpotent (p : Γ(Spec (.of C), U)))

/- Lemma 60.21.4: the completed de Rham complex of the smooth connection
corresponding to a quasi-coherent crystal computes derived crystalline sections. -/
@[stacks 07LH] #check
  (CrystallineModuleSheaf.CrisModuleSheaf.Completed.Smooth.deRham_computes R IS γS hc
    x₀ (Iso.refl _) ((Category.id_comp _).trans hx₀) hI hγ F s h_p :
    IsIsomorphic
      (CrystallineModuleSheaf.derivedGlobalSections p (Spec (.of A)) IS γS hc s
        (Spec (.of C)) x₀ h_p F.obj)
      (DerivedCategory.Q.obj
        ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}).obj
          ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex
            (ComplexShape.up ℕ)).obj
              (CrystallineModuleSheaf.CrisModuleSheaf.Completed.Smooth.deRhamComplex R IS γS hc
                x₀ (Iso.refl _) ((Category.id_comp _).trans hx₀) hI hγ F)))))

variable (n : ℕ)

/- Degreewise crystalline cohomology is the homology of the same smooth completed de Rham complex. -/
#check
  (CrystallineModuleSheaf.CrisModuleSheaf.Completed.Smooth.cohomology_computes R IS γS hc
    x₀ (Iso.refl _) ((Category.id_comp _).trans hx₀) hI hγ F s h_p n :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (n : ℤ)).obj
        (CrystallineModuleSheaf.derivedGlobalSections p (Spec (.of A)) IS γS hc s
          (Spec (.of C)) x₀ h_p F.obj))
      (((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (CrystallineModuleSheaf.CrisModuleSheaf.Completed.Smooth.deRhamComplex R IS γS hc
            x₀ (Iso.refl _) ((Category.id_comp _).trans hx₀) hI hγ F)).homology n))
