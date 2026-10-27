/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Completed.Connection
public import Mathlib.CategoryTheory.Equivalence

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

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

/-- The canonical completed-connection functor on quasi-coherent crystals is faithful. -/
instance toConnectionPairs_faithful :
    (toConnectionPairs p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).Faithful := sorry

/-- The canonical completed-connection functor on quasi-coherent crystals is full. -/
instance toConnectionPairs_full :
    (toConnectionPairs p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).Full := sorry

/-- Every complete integrable topologically quasi-nilpotent connection is isomorphic to
the canonical completed connection of a quasi-coherent crystal. -/
instance toConnectionPairs_essSurj :
    (toConnectionPairs p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).EssSurj := sorry

/-- The canonical completed-connection functor on quasi-coherent crystals is an equivalence
of categories with complete integrable topologically quasi-nilpotent connections. -/
instance toConnectionPairs_isEquivalence :
    (toConnectionPairs p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ).IsEquivalence :=
  { faithful := toConnectionPairs_faithful p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ
    full := toConnectionPairs_full p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ
    essSurj := toConnectionPairs_essSurj p γ π hπ hJ hIC hpnil E hE IS γS hc x₀ eX heX hI hγ }

end CrystallineModuleSheaf.CrisModuleSheaf.Completed
