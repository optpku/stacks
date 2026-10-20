module

public import Mathlib.RingTheory.Finiteness.Defs
public import ReasLib.RingTheory.Localization.AtPrime.Map
public import ReasLib.RingTheory.RingHom.Cokernel.IdealPower

@[expose] public section

universe u

namespace RingHom.MaximalPatching

variable {A : Type u} [CommRing A] [hA : IsNoetherianRing A]
variable {r : ℕ} (m : Fin r → Ideal A) [∀ i, (m i).IsMaximal]
variable (hm : Function.Injective m)
variable (B : Fin r → Type u) [∀ i, CommRing (B i)]
variable (φ : ∀ i, Localization.AtPrime (m i) →+* B i)

include hA hm

/-- Ring homomorphisms from the localizations at a finite family of pairwise distinct maximal
ideals, with ideal-power-annihilated kernels and additive cokernels, patch to a global ring
homomorphism with the corresponding properties for the intersection ideal. -/
theorem «exists»
    (hker : ∀ i, Module.IsAnnihilatedByPower
      (Ideal.map (algebraMap A (Localization.AtPrime (m i))) (m i))
      (RingHom.ker (φ i)))
    (hcoker : ∀ i, RingHom.Cokernel.IsAnnihilatedByPower
      (Ideal.map (algebraMap A (Localization.AtPrime (m i))) (m i)) (φ i)) :
    ∃ (C : Type u) (_ : CommRing C) (ψ : A →+* C)
        (e : ∀ i, Localization (Submonoid.map ψ (m i).primeCompl) ≃+* B i)
        (_ : ∀ i, (e i).toRingHom.comp (Localization.AtPrime.map ψ (m i)) = φ i)
        (_ : Module.IsAnnihilatedByPower (⨅ i, m i) (RingHom.ker ψ)),
      RingHom.Cokernel.IsAnnihilatedByPower (⨅ i, m i) ψ := sorry

/-- If the local ring homomorphisms in maximal-ideal patching are finite, the global ring
homomorphism may also be chosen finite. -/
theorem existsFinite
    (hfinite : ∀ i, (φ i).Finite)
    (hker : ∀ i, Module.IsAnnihilatedByPower
      (Ideal.map (algebraMap A (Localization.AtPrime (m i))) (m i))
      (RingHom.ker (φ i)))
    (hcoker : ∀ i, RingHom.Cokernel.IsAnnihilatedByPower
      (Ideal.map (algebraMap A (Localization.AtPrime (m i))) (m i)) (φ i)) :
    ∃ (C : Type u) (_ : CommRing C) (ψ : A →+* C) (_ : ψ.Finite)
        (e : ∀ i, Localization (Submonoid.map ψ (m i).primeCompl) ≃+* B i)
        (_ : ∀ i, (e i).toRingHom.comp (Localization.AtPrime.map ψ (m i)) = φ i)
        (_ : Module.IsAnnihilatedByPower (⨅ i, m i) (RingHom.ker ψ)),
      RingHom.Cokernel.IsAnnihilatedByPower (⨅ i, m i) ψ := sorry

/-- If the local ring homomorphisms in maximal-ideal patching are injective, the global ring
homomorphism may also be chosen injective. -/
theorem existsInjective
    (hker : ∀ i, Module.IsAnnihilatedByPower
      (Ideal.map (algebraMap A (Localization.AtPrime (m i))) (m i))
      (RingHom.ker (φ i)))
    (hcoker : ∀ i, RingHom.Cokernel.IsAnnihilatedByPower
      (Ideal.map (algebraMap A (Localization.AtPrime (m i))) (m i)) (φ i))
    (hinjective : ∀ i, Function.Injective (φ i)) :
    ∃ (C : Type u) (_ : CommRing C) (ψ : A →+* C)
        (e : ∀ i, Localization (Submonoid.map ψ (m i).primeCompl) ≃+* B i)
        (_ : ∀ i, (e i).toRingHom.comp (Localization.AtPrime.map ψ (m i)) = φ i)
        (_ : Module.IsAnnihilatedByPower (⨅ i, m i) (RingHom.ker ψ))
        (_ : RingHom.Cokernel.IsAnnihilatedByPower (⨅ i, m i) ψ),
      Function.Injective ψ := sorry

/-- If the local ring homomorphisms in maximal-ideal patching are surjective, the global ring
homomorphism may also be chosen surjective. -/
theorem existsSurjective
    (hker : ∀ i, Module.IsAnnihilatedByPower
      (Ideal.map (algebraMap A (Localization.AtPrime (m i))) (m i))
      (RingHom.ker (φ i)))
    (hcoker : ∀ i, RingHom.Cokernel.IsAnnihilatedByPower
      (Ideal.map (algebraMap A (Localization.AtPrime (m i))) (m i)) (φ i))
    (hsurjective : ∀ i, Function.Surjective (φ i)) :
    ∃ (C : Type u) (_ : CommRing C) (ψ : A →+* C)
        (e : ∀ i, Localization (Submonoid.map ψ (m i).primeCompl) ≃+* B i)
        (_ : ∀ i, (e i).toRingHom.comp (Localization.AtPrime.map ψ (m i)) = φ i)
        (_ : Module.IsAnnihilatedByPower (⨅ i, m i) (RingHom.ker ψ))
        (_ : RingHom.Cokernel.IsAnnihilatedByPower (⨅ i, m i) ψ),
      Function.Surjective ψ := sorry

end RingHom.MaximalPatching

end
