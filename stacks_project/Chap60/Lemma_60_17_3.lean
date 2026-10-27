/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Completed.Connection
import StacksCheckRecall

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory
open CrystallineModuleSheaf.CrisModuleSheaf.Completed

universe u

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

/- Lemma 60.17.3: crystals in quasi-coherent modules determine complete integrable
connections satisfying (07JB), (07JC), (07JD), and (07JE), on the inverse limit of
sections over the polynomial-envelope quotient thickenings. -/
@[stacks 07JG] #check
  (CrystallineModuleSheaf.CrisModuleSheaf.Completed.toConnectionPairs
    p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ :
    quasiCoherentCrystals IS γS hc x₀ ⥤
      -- Local instance justification (noncanonical choice): the relative connection uses the coefficient algebra selected by the explicit polynomial envelope.
      letI := DividedPowerEnvelope.Coordinates.baseAlgebra E
      Connection.Adic.quasiNilpotentCategory (A := A) (δ := E.D.dividedPowers)
        (DividedPowerEnvelope.Coordinates.completedCoord E hE p))

