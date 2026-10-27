/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Completed.Smooth
public import ReasLib.AlgebraicGeometry.Crystalline.Affine
public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.GlobalSections
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Crystalline
open DividedPowerEnvelope CrystallineModuleSheaf

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

namespace CrystallineModuleSheaf.CrisModuleSheaf.Completed.Smooth

variable {p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE'}


variable {X : Scheme.{u}} (IS : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (IS.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen f))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom)
variable (x₀ : X ⟶ IS.subscheme) (eX : Spec (.of C) ≅ X)
variable (heX : eX.hom ≫ x₀ ≫ IS.subschemeι = Spec.map (CommRingCat.ofHom (algebraMap A C)))
variable (hI : Affine.idealCompatible I IS)
variable (hγ : Affine.dividedPowersCompatible I γ IS γS)
variable (F : quasiCoherentCrystals IS γS hc x₀)

/-- The completed de Rham complex of the actual smooth connection associated with a quasi-coherent crystal. -/
def deRhamComplex : CochainComplex AddCommGrpCat.{u} ℕ :=
  -- Local instance justification (noncanonical choice): the smooth connection uses the structural coefficient action of its envelope.
  letI := (E'.toD.comp (algebraMap A P')).toAlgebra
  let V := (CrystallineModuleSheaf.CrisModuleSheaf.Completed.Smooth.toConnectionPairs R
    IS γS hc x₀ eX heX hI hγ).obj F
  Connection.Adic.deRhamComplex A E'.D E'.D.dividedPowers p V.2.val V.2.property.2.1

variable (s : Spec (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/-- The completed de Rham complex of the smooth crystalline connection computes derived crystalline sections. -/
theorem deRham_computes :
    IsIsomorphic
      (CrystallineModuleSheaf.derivedGlobalSections p (Spec (.of A)) IS γS hc s X x₀ h_p F.obj)
      (DerivedCategory.Q.obj
        ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}).obj
          ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex
            (ComplexShape.up ℕ)).obj
              (deRhamComplex R IS γS hc x₀ eX heX hI hγ F)))) := sorry

/-- Crystalline cohomology is the degreewise homology of the universe-raised smooth completed de Rham complex. -/
theorem cohomology_computes (n : ℕ) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (n : ℤ)).obj
        (CrystallineModuleSheaf.derivedGlobalSections p (Spec (.of A)) IS γS hc s X x₀ h_p F.obj))
      (((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (deRhamComplex R IS γS hc x₀ eX heX hI hγ F)).homology n) := sorry

end CrystallineModuleSheaf.CrisModuleSheaf.Completed.Smooth
