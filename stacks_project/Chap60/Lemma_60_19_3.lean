module

public import ReasLib.RingTheory.DividedPowers.DeRham.Cosimplicial.ExteriorPower
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 60.19.3: for every cosimplicial module over the crystalline completed
ring diagram and every positive degree, the completed tensor product with the
completed exterior power of differentials is homotopic to zero. -/
@[stacks 07LA] #check (crystallineOmegaPowerTensor_homotopic_zero :
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
    (E : (n : ℕ) →
      DividedPowerEnvelope I γ (algebraMap A (MvPolynomial.TensorPower.carrier A ι n))
        (J n) (hIJ n))
    (hE : ∀ n, DividedPowerEnvelope.IsUniversal γ
      (algebraMap A (MvPolynomial.TensorPower.carrier A ι n)) (hIJ n) (E n))
    (γbar : (n : ℕ) → DividedPowers (Crystalline.dnIdeal p I γ J hIJ E n))
    (hγbar : ∀ n, DividedPowers.IsDPMorphism (E n).D.dividedPowers (γbar n)
      (algebraMap (E n).D (AdicCompletion (Ideal.span {(p : (E n).D)}) (E n).D)))
    (M : PresheafOfModules.{u}
      (moduleRingPresheaf (Crystalline.dStar p I γ π J hJ hIJ E hE)))
    (i : ℕ) (hi : 0 < i),
    CosimplicialModule.Homotopic
      (𝟙 (Crystalline.omegaPowerTensor p I γ π J hJ hIJ E hE γbar hγbar i M))
      (0 :
        Crystalline.omegaPowerTensor p I γ π J hJ hIJ E hE γbar hγbar i M ⟶
          Crystalline.omegaPowerTensor p I γ π J hJ hIJ E hE γbar hγbar i M))
