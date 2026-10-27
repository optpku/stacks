/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Completed.Smooth.DeRham
public import stacks_project.Chap60.Lemma_60_17_5_Completion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory DividedPowerEnvelope

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

/- Lemma 60.17.5 (1): a smooth surjective presentation admits a finite polynomial
completed-envelope presentation and compatible divided-power retract maps. -/
@[stacks 07L5] #check
  (DividedPowerEnvelope.PolynomialRetract.exists p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE' :
    Nonempty (DividedPowerEnvelope.PolynomialRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE'))

variable (R : DividedPowerEnvelope.PolynomialRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')

/- Lemma 60.17.5 (2): completed scalar extension along the retract maps gives an
equivalence between the categories of complete integrable quasi-nilpotent connections. -/
@[stacks 07L5] #check
  (CrystallineModuleSheaf.CrisModuleSheaf.Completed.Smooth.baseChange_isEquivalence R :
    (CrystallineModuleSheaf.CrisModuleSheaf.Completed.Smooth.baseChange R).IsEquivalence)

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

/- Lemma 60.17.5 (3): the canonical functor from quasi-coherent crystals to
smooth completed-envelope connections is an equivalence. -/
@[stacks 07L5] #check
  (CrystallineModuleSheaf.CrisModuleSheaf.Completed.Smooth.toConnectionPairs_isEquivalence R IS γS hc x₀ eX heX hI hγ :
    (CrystallineModuleSheaf.CrisModuleSheaf.Completed.Smooth.toConnectionPairs R IS γS hc x₀ eX heX hI hγ).IsEquivalence)
