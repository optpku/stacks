module

public import stacks_project.Chap60.Remark_60_17_6_Lifting
public import stacks_project.Chap60.Remark_60_17_6_Retract
public import stacks_project.Chap60.Remark_60_17_6_Equivalence
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
variable [Algebra.HasStrongLifting A P']
variable (R : LiftingRetract p I γ π' hπ' J' hJ' hIC hpnil hIJ' E' hE')
variable {S : Scheme.{u}} {IS : S.IdealSheafData}
variable {γS : ∀ V : S.affineOpens, DividedPowers (IS.ideal V)}
variable {h_compatible :
    ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γS V).IsDPMorphism (γS (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ IS.subscheme}

/-- Remark 60.17.6: in Situation 60.5.1, the equivalence of Proposition 60.17.4
still holds if we start with a surjection `P' → C` where `P'/A` satisfies the
strong lifting property of Algebra, Lemma 10.138.17, rather than a polynomial
algebra. The argument is the retract construction of Lemma 60.17.5; the rings
`D(n)` of a polynomial presentation remain `p`-adic completions of divided
power polynomial rings. -/
@[stacks 07L6, instance]
instance crystalsToConnectionPairsOverLifting_isEquivalence
    (T : smallCrystallineSite S IS γS h_compatible X x₀)
    (moduleT : ∀ F : QuasiCoherentCrystal S IS γS h_compatible X x₀,
      Module (crystallineD p I γ R.π R.hπ R.J R.hJ hIC hpnil R.hIJ R.E R.hE)
        (CrisModuleSheaf.sectionModule F.obj T)) :
    (CrystallineModuleSheaf.crystalsToConnectionPairsOverLifting p I γ π' hπ' J' hJ'
        hIC hpnil hIJ' E' hE' R T moduleT).IsEquivalence :=
  sorry


end
