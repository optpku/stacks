/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Localization.AtPrime.MaximalPatching
import StacksCheckRecall

@[expose] public section

universe u

variable {A : Type u} [CommRing A] [hA : IsNoetherianRing A]
variable {r : ℕ} (m : Fin r → Ideal A) [∀ i, (m i).IsMaximal]
variable (hm : Function.Injective m)
variable (B : Fin r → Type u) [∀ i, CommRing (B i)]
variable (φ : ∀ i, Localization.AtPrime (m i) →+* B i)

/- Lemma 42.4.1: ring maps from the localizations at a finite family of pairwise distinct
maximal ideals, with kernels and additive cokernels annihilated by powers of the corresponding
extended ideals, patch to a global ring map with the same properties for the intersection. -/
@[stacks 0EAE] #check
  (RingHom.MaximalPatching.«exists» m hm B φ :
    ∀ (hker : ∀ i, Module.IsAnnihilatedByPower
        (Ideal.map (algebraMap A (Localization.AtPrime (m i))) (m i))
        (RingHom.ker (φ i)))
      (hcoker : ∀ i, RingHom.Cokernel.IsAnnihilatedByPower
        (Ideal.map (algebraMap A (Localization.AtPrime (m i))) (m i)) (φ i)),
      ∃ (C : Type u) (_ : CommRing C) (ψ : A →+* C)
          (e : ∀ i, Localization (Submonoid.map ψ (m i).primeCompl) ≃+* B i)
          (_ : ∀ i, (e i).toRingHom.comp
            (Localization.AtPrime.map ψ (m i)) = φ i)
          (_ : Module.IsAnnihilatedByPower (⨅ i, m i) (RingHom.ker ψ)),
        RingHom.Cokernel.IsAnnihilatedByPower (⨅ i, m i) ψ)

#check
  (RingHom.MaximalPatching.existsFinite m hm B φ :
    ∀ (hfinite : ∀ i, (φ i).Finite)
      (hker : ∀ i, Module.IsAnnihilatedByPower
        (Ideal.map (algebraMap A (Localization.AtPrime (m i))) (m i))
        (RingHom.ker (φ i)))
      (hcoker : ∀ i, RingHom.Cokernel.IsAnnihilatedByPower
        (Ideal.map (algebraMap A (Localization.AtPrime (m i))) (m i)) (φ i)),
      ∃ (C : Type u) (_ : CommRing C) (ψ : A →+* C) (_ : ψ.Finite)
          (e : ∀ i, Localization (Submonoid.map ψ (m i).primeCompl) ≃+* B i)
          (_ : ∀ i, (e i).toRingHom.comp
            (Localization.AtPrime.map ψ (m i)) = φ i)
          (_ : Module.IsAnnihilatedByPower (⨅ i, m i) (RingHom.ker ψ)),
        RingHom.Cokernel.IsAnnihilatedByPower (⨅ i, m i) ψ)

#check
  (RingHom.MaximalPatching.existsInjective m hm B φ :
    ∀ (hker : ∀ i, Module.IsAnnihilatedByPower
        (Ideal.map (algebraMap A (Localization.AtPrime (m i))) (m i))
        (RingHom.ker (φ i)))
      (hcoker : ∀ i, RingHom.Cokernel.IsAnnihilatedByPower
        (Ideal.map (algebraMap A (Localization.AtPrime (m i))) (m i)) (φ i))
      (hinjective : ∀ i, Function.Injective (φ i)),
      ∃ (C : Type u) (_ : CommRing C) (ψ : A →+* C)
          (e : ∀ i, Localization (Submonoid.map ψ (m i).primeCompl) ≃+* B i)
          (_ : ∀ i, (e i).toRingHom.comp
            (Localization.AtPrime.map ψ (m i)) = φ i)
          (_ : Module.IsAnnihilatedByPower (⨅ i, m i) (RingHom.ker ψ))
          (_ : RingHom.Cokernel.IsAnnihilatedByPower (⨅ i, m i) ψ),
        Function.Injective ψ)

#check
  (RingHom.MaximalPatching.existsSurjective m hm B φ :
    ∀ (hker : ∀ i, Module.IsAnnihilatedByPower
        (Ideal.map (algebraMap A (Localization.AtPrime (m i))) (m i))
        (RingHom.ker (φ i)))
      (hcoker : ∀ i, RingHom.Cokernel.IsAnnihilatedByPower
        (Ideal.map (algebraMap A (Localization.AtPrime (m i))) (m i)) (φ i))
      (hsurjective : ∀ i, Function.Surjective (φ i)),
      ∃ (C : Type u) (_ : CommRing C) (ψ : A →+* C)
          (e : ∀ i, Localization (Submonoid.map ψ (m i).primeCompl) ≃+* B i)
          (_ : ∀ i, (e i).toRingHom.comp
            (Localization.AtPrime.map ψ (m i)) = φ i)
          (_ : Module.IsAnnihilatedByPower (⨅ i, m i) (RingHom.ker ψ))
          (_ : RingHom.Cokernel.IsAnnihilatedByPower (⨅ i, m i) ψ),
        Function.Surjective ψ)

end
