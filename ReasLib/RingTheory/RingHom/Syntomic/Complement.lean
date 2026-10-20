/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.Syntomic.AtPrime

/-!
# Syntomicity on the complement of a closed set
-/

@[expose] public section

universe u v

namespace RingHom

/-- A ring homomorphism is syntomic on the complement of `V(I)` if it is
syntomic at every prime of the target outside `PrimeSpectrum.zeroLocus I`. -/
def SyntomicOnComplement {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal S) : Prop :=
  ∀ q : PrimeSpectrum S, q ∉ PrimeSpectrum.zeroLocus I → f.SyntomicAtPrime q

namespace SyntomicOnComplement

/-- Syntomicity on the complement of `V(I)` is equivalent to syntomicity of
`R → S_g` for every `g ∈ I`. -/
theorem iff_forall_away {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal S) :
    f.SyntomicOnComplement I ↔
      ∀ g ∈ I, ((algebraMap S (Localization.Away g)).comp f).Syntomic :=
  sorry

end SyntomicOnComplement

end RingHom

end
