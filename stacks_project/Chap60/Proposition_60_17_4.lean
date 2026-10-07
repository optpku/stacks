module

public import stacks_project.Chap60.Proposition_60_17_4_Categories
public import stacks_project.Chap60.Proposition_60_17_4_Functor
import Mathlib.Tactic.CrossRefAttribute

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

/-- Proposition 60.17.4: in the situation of 60.17.0.1–60.17.0.3, the functor of
Lemma 60.17.3 from crystals in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)`
to pairs `(M, ∇)` satisfying (07JB), (07JC), (07JD), and (07JE) is an
equivalence of categories. -/
@[stacks 07JH, instance]
instance crystalsToConnectionPairs_isEquivalence
    (T : smallCrystallineSite S IS γS h_compatible X x₀)
    (moduleT : ∀ F : QuasiCoherentCrystal S IS γS h_compatible X x₀,
      Module (crystallineD p I γ π hπ J hJ hIC hpnil hIJ E hE)
        (CrisModuleSheaf.sectionModule F.obj T)) :
    (crystalsToConnectionPairs p I γ π hπ J hJ hIC hpnil hIJ E hE γbar T
        moduleT).IsEquivalence :=
  sorry

end
