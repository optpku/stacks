/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Equivalence
public import stacks_project.Chap60.Proposition_60_17_4_Categories
public import stacks_project.Chap60.Lemma_60_17_3_Functor
public import stacks_project.Chap60.Lemma_60_15_1

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf
open CrystallineConnectionPair

universe u

variable {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
variable [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
variable (I : Ideal A) (γ : DividedPowers I)
variable {C : Type u} [CommRing C] [Algebra A C]
variable {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
variable (hπ : Function.Surjective π)
variable (J : Ideal (MvPolynomial ι A))
variable (hJ : J = RingHom.ker π.toRingHom)
variable (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
variable (hpnil : IsNilpotent (p : C))
variable (hIJ : Ideal.map (algebraMap A (MvPolynomial ι A)) I ≤ J)
variable (E : DividedPowerEnvelope I γ (algebraMap A (MvPolynomial ι A)) J hIJ)
variable (hE : DividedPowerEnvelope.IsUniversal γ
  (algebraMap A (MvPolynomial ι A)) hIJ E)
variable (γbar : DividedPowers
  (Ideal.map (algebraMap E.D
    (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)) E.D.ideal))
variable {S : Scheme.{u}} {IS : S.IdealSheafData}
variable {γS : ∀ V : S.affineOpens, DividedPowers (IS.ideal V)}
variable {h_compatible :
    ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γS V).IsDPMorphism (γS (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ IS.subscheme}

namespace CrystallineModuleSheaf

/-- Evaluation of crystals in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)`
as a functor to completed connection pairs satisfying (07JB)–(07JE). -/
noncomputable def crystalsToConnectionPairs
    (T : smallCrystallineSite S IS γS h_compatible X x₀)
    (moduleT : ∀ F : QuasiCoherentCrystal S IS γS h_compatible X x₀,
      Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
        (CrisModuleSheaf.sectionModule F.obj T)) :
    QuasiCoherentCrystal S IS γS h_compatible X x₀ ⥤
      ConnectionPairCat p I γ π hπ J hJ hIC hpnil hIJ E hE γbar where
  obj F :=
    ConnectionPairCat.of p I γ π hπ J hJ hIC hpnil hIJ E hE γbar
      (@crystalToConnectionPair A _ p _ _ I γ C _ _ ι π hπ J hJ hIC hpnil hIJ E hE γbar
        S IS γS h_compatible X x₀ F.obj F.property.isCrystal
        F.property.isLocallyQuasiCoherent T (moduleT F))
  map {F G} φ :=
    @crystalToConnectionPair_map A _ p _ _ I γ C _ _ ι π hπ J hJ hIC hpnil hIJ E hE γbar
      S IS γS h_compatible X x₀ F.obj G.obj F.property.isCrystal G.property.isCrystal
      F.property.isLocallyQuasiCoherent G.property.isLocallyQuasiCoherent φ.hom T
      (moduleT F) (moduleT G)
  map_id := sorry
  map_comp := sorry

/-- Object assignment of `crystalsToConnectionPairs` recovers
`crystalToConnectionPair`. -/
theorem crystalsToConnectionPairs_obj
    (T : smallCrystallineSite S IS γS h_compatible X x₀)
    (moduleT : ∀ F : QuasiCoherentCrystal S IS γS h_compatible X x₀,
      Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
        (CrisModuleSheaf.sectionModule F.obj T))
    (F : QuasiCoherentCrystal S IS γS h_compatible X x₀) :
    ((crystalsToConnectionPairs p I γ π hπ J hJ hIC hpnil hIJ E hE γbar T
          moduleT).obj F).pair =
      @crystalToConnectionPair A _ p _ _ I γ C _ _ ι π hπ J hJ hIC hpnil hIJ E hE γbar
        S IS γS h_compatible X x₀ F.obj F.property.isCrystal
        F.property.isLocallyQuasiCoherent T (moduleT F) :=
  sorry

/-- Morphisms of `crystalsToConnectionPairs` recover
`crystalToConnectionPair_map`. -/
theorem crystalsToConnectionPairs_map
    (T : smallCrystallineSite S IS γS h_compatible X x₀)
    (moduleT : ∀ F : QuasiCoherentCrystal S IS γS h_compatible X x₀,
      Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
        (CrisModuleSheaf.sectionModule F.obj T))
    {F G : QuasiCoherentCrystal S IS γS h_compatible X x₀} (φ : F ⟶ G) :
    (crystalsToConnectionPairs p I γ π hπ J hJ hIC hpnil hIJ E hE γbar T
        moduleT).map φ =
      @crystalToConnectionPair_map A _ p _ _ I γ C _ _ ι π hπ J hJ hIC hpnil hIJ E hE
        γbar S IS γS h_compatible X x₀ F.obj G.obj F.property.isCrystal
        G.property.isCrystal F.property.isLocallyQuasiCoherent
        G.property.isLocallyQuasiCoherent φ.hom T (moduleT F) (moduleT G) :=
  sorry

end CrystallineModuleSheaf

end
