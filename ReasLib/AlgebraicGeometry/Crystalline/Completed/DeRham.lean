/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Completed.Connection
public import ReasLib.AlgebraicGeometry.Crystalline.Cohomology.GlobalSections
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Crystalline

universe u

namespace CrystallineModuleSheaf.CrisModuleSheaf.Completed

variable (p : ℕ) [Fact p.Prime]
variable {A C ι : Type u} [CommRing A] [CommRing C] [Algebra A C]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {I : Ideal A} (γ : DividedPowers I)
variable (π : MvPolynomial ι A →ₐ[A] C) (hπ : Function.Surjective π)
variable {J : Ideal (MvPolynomial ι A)} (hJ : J = RingHom.ker π.toRingHom)
variable (hIC : Ideal.map (algebraMap A C) I = ⊥) (hpnil : IsNilpotent (p : C))
variable {hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J}
variable (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
variable (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A (MvPolynomial ι A)) hIJ E)
variable {X : Scheme.{u}} (IS : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (IS.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (f : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen f))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le f)).op).hom)
variable (x₀ : X ⟶ IS.subscheme) (eX : Spec (.of C) ≅ X)
variable (heX : eX.hom ≫ x₀ ≫ IS.subschemeι = Spec.map (CommRingCat.ofHom (algebraMap A C)))
variable (hI : IS = DividedPowers.affineIdeal (I := I))
variable (hγ : DividedPowers.IsDPMorphism γ
  (γS ⟨⊤, isAffineOpen_top (Spec (.of A))⟩) (Scheme.ΓSpecIso (.of A)).inv.hom)
variable (F : CrisModuleSheaf (Spec (.of A)) IS γS hc X x₀)
variable [IsCrystal F] [IsLocallyQuasiCoherent F]

/-- The completed de Rham complex of the canonical integrable connection on the
inverse-limit coefficients of a quasi-coherent crystal on an affine scheme. -/
def deRhamComplex : CochainComplex AddCommGrpCat.{u} ℕ :=
  -- Local instance justification (noncanonical choice): the explicit universal envelope selects the coefficient algebra used by its relative divided-power connection.
  letI := DividedPowerEnvelope.Coordinates.baseAlgebra E
  Connection.Adic.deRhamComplex A E.D E.D.dividedPowers p
    (M := coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F)
    (connection p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F)
    (connection_isIntegrable p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F)

/-- Degree zero of the completed crystalline de Rham complex is the inverse limit
of the coefficient modules on the completed-envelope quotient thickenings. -/
theorem deRhamComplex_X_zero :
    (deRhamComplex p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F).X 0 =
      AddCommGrpCat.of
        (coefficientModule p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F) := sorry

variable (s : Spec.{u} (.of A) ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/-- The completed de Rham complex of a quasi-coherent crystal on an affine scheme
computes its crystalline derived global sections. -/
theorem deRhamComplex_computes :
    IsIsomorphic
      (CrystallineModuleSheaf.derivedGlobalSections p (Spec (.of A)) IS γS hc s X x₀ h_p F)
      (DerivedCategory.Q.obj
        ((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}).obj
          ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex
            (ComplexShape.up ℕ)).obj
              (deRhamComplex p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F)))) := sorry

/-- Crystalline cohomology of a quasi-coherent crystal on an affine scheme is the
homology of its universe-raised completed de Rham complex. -/
theorem deRhamComplex_cohomology (n : ℕ) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (n : ℤ)).obj
        (CrystallineModuleSheaf.derivedGlobalSections p (Spec (.of A)) IS γS hc s X x₀ h_p F))
      (((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
          (deRhamComplex p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ F)).homology n) := sorry

end CrystallineModuleSheaf.CrisModuleSheaf.Completed
