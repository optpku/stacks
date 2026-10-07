module

public import stacks_project.Chap60.Lemma_60_17_3_Functor
public import stacks_project.Chap60.Lemma_60_17_3_Pair
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf
open CrystallineConnectionPair
open scoped TensorProduct

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

/-- Lemma 60.17.3 (1): in the situation of 60.17.0.1–60.17.0.3 the assignment
from crystals in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)` to pairs
`(M, ∇)` satisfying (07JB), (07JC), (07JD), and (07JE) preserves identity
morphisms, sending `F` to `crystalToConnectionPair F T`. -/
@[stacks 07JG]
theorem crystalsToConnectionPairs_map_id
    (T : smallCrystallineSite S IS γS h_compatible X x₀)
    (F : CrisModuleSheaf S IS γS h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F] [CrisModuleSheaf.IsLocallyQuasiCoherent F]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (CrisModuleSheaf.sectionModule F T)] :
    crystalToConnectionPair_map p I γ π hπ J hJ hIC hpnil hIJ E hE γbar (𝟙 F) T =
      Hom.id p I γ π hπ J hJ hIC hpnil hIJ E hE γbar
        (crystalToConnectionPair p I γ π hπ J hJ hIC hpnil hIJ E hE γbar F T) :=
  sorry

/-- Lemma 60.17.3 (2): in the situation of 60.17.0.1–60.17.0.3 the assignment
from crystals in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)` to pairs
`(M, ∇)` satisfying (07JB), (07JC), (07JD), and (07JE) preserves composition
of morphisms. -/
@[stacks 07JG]
theorem crystalsToConnectionPairs_map_comp
    (T : smallCrystallineSite S IS γS h_compatible X x₀)
    {F G H : CrisModuleSheaf S IS γS h_compatible X x₀}
    [CrisModuleSheaf.IsCrystal F] [CrisModuleSheaf.IsCrystal G]
    [CrisModuleSheaf.IsCrystal H]
    [CrisModuleSheaf.IsLocallyQuasiCoherent F]
    [CrisModuleSheaf.IsLocallyQuasiCoherent G]
    [CrisModuleSheaf.IsLocallyQuasiCoherent H]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (CrisModuleSheaf.sectionModule F T)]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (CrisModuleSheaf.sectionModule G T)]
    [Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
      (CrisModuleSheaf.sectionModule H T)]
    (φ : F ⟶ G) (ψ : G ⟶ H) :
    crystalToConnectionPair_map p I γ π hπ J hJ hIC hpnil hIJ E hE γbar (φ ≫ ψ) T =
      Hom.comp p I γ π hπ J hJ hIC hpnil hIJ E hE γbar
        (crystalToConnectionPair_map p I γ π hπ J hJ hIC hpnil hIJ E hE γbar φ T)
        (crystalToConnectionPair_map p I γ π hπ J hJ hIC hpnil hIJ E hE γbar ψ T) :=
  sorry
