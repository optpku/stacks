/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Completed.Lifting
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline

universe u

variable (p : ℕ) [Fact p.Prime]
variable {A C P : Type u} [CommRing A] [CommRing C] [CommRing P]
variable [Algebra A C] [Algebra A P]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable {I : Ideal A} (γ : DividedPowers I)
variable (π : P →ₐ[A] C) (hπ : Function.Surjective π)
variable {J : Ideal P} (hJ : J = RingHom.ker π.toRingHom)
variable (hIC : Ideal.map (algebraMap A C) I = ⊥) (hpnil : IsNilpotent (p : C))
variable {hIJ : Ideal.map (algebraMap A P) I ≤ J}
variable (E : DividedPowerEnvelope I γ (algebraMap A P) J hIJ)
variable (hE : DividedPowerEnvelope.IsUniversal γ (algebraMap A P) hIJ E)

variable [Algebra.HasStrongLifting A P]

variable {X : Scheme.{u}} (IS : (Spec (.of A)).IdealSheafData)
variable (γS : ∀ V : (Spec (.of A)).affineOpens, DividedPowers (IS.ideal V))
variable (hc : ∀ (V : (Spec (.of A)).affineOpens) (a : Γ(Spec (.of A), V)),
  (γS V).IsDPMorphism (γS ((Spec (.of A)).affineBasicOpen a))
    ((Spec (.of A)).presheaf.map (homOfLE ((Spec (.of A)).basicOpen_le a)).op).hom)
variable (x₀ : X ⟶ IS.subscheme) (eX : Spec (.of C) ≅ X)
variable (heX : eX.hom ≫ x₀ ≫ IS.subschemeι = Spec.map (CommRingCat.ofHom (algebraMap A C)))
variable (hI : IS = DividedPowers.affineIdeal (I := I))
variable (hγ : DividedPowers.IsDPMorphism γ
  (γS ⟨⊤, isAffineOpen_top (Spec (.of A))⟩) (Scheme.ΓSpecIso (.of A)).inv.hom)

/- Remark 60.17.6. The crystalline equivalence holds for a surjective algebra presentation
with the strong lifting property across locally nilpotent ideals, in the affine divided-power
setup. Polynomial presentations simplify the algebra of the completed divided-power envelopes. -/
@[stacks 07L6] #check
  (CrystallineModuleSheaf.CrisModuleSheaf.Completed.Lifting.toConnectionPairs_isEquivalence
    p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ :
    (CrystallineModuleSheaf.CrisModuleSheaf.Completed.Lifting.toConnectionPairs
      p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).IsEquivalence)
