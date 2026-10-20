module

public import ReasLib.RingTheory.DividedPowers.DeRham.Cosimplicial
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 60.19.2
The completed differential cosimplicial module is homotopic to zero over the completed envelope diagram.
-/
@[stacks 07L9] #check (crystallineOmegaDStar_homotopic_zero :
  ∀ {A : Type u} [CommRing A] (p : ℕ) [Fact (Nat.Prime p)]
    [Algebra (Localization.AtPrime (Ideal.span ({(p : ℤ)} : Set ℤ))) A]
    (I : Ideal A) (γ : DividedPowers I)
    {C : Type u} [CommRing C] [Algebra A C]
    {ι : Type u} (π : MvPolynomial ι A →ₐ[A] C)
    (hπ : Function.Surjective π)
    (hIC : Ideal.map (algebraMap A C) I = (⊥ : Ideal C))
    (hpnil : IsNilpotent (p : C))
    (J : (n : ℕ) → Ideal (MvPolynomial.TensorPower.carrier A ι n))
    (hJ : ∀ n, J n = RingHom.ker (MvPolynomial.TensorPower.diagonal A ι π n).toRingHom)
    (hIJ : ∀ n, Ideal.map (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) I ≤ J n)
    (E : (n : ℕ) → DividedPowerEnvelope I γ
      (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) (J n) (hIJ n))
    (hE : ∀ n, DividedPowerEnvelope.IsUniversal γ
      (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) (hIJ n) (E n))
    (γbar : (n : ℕ) → DividedPowers (Crystalline.dnIdeal p I γ J hIJ E n))
    (hγbar : ∀ n, DividedPowers.IsDPMorphism (E n).D.dividedPowers (γbar n)
      (algebraMap (E n).D (AdicCompletion (Ideal.span {(p : (E n).D)}) (E n).D))),
    CosimplicialModule.Homotopic
      (𝟙 (Crystalline.omegaDStar p I γ π J hJ hIJ E hE γbar hγbar))
      (0 : Crystalline.omegaDStar p I γ π J hJ hIJ E hE γbar hγbar ⟶
        Crystalline.omegaDStar p I γ π J hJ hIJ E hE γbar hγbar))
