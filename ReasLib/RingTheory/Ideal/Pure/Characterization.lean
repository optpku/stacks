/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Ideal.Pure
public import Mathlib.RingTheory.Support
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.OneAdd

/-!
# Characterizations of pure ideals

@stack 04PS

This leaf packages the algebraic, local, topological, and localization
criteria for purity of an ideal.
-/

@[expose] public section

universe u

namespace Ideal.Pure

/-- Lemma 10.108.2 (Stacks `04PS`): the standard eleven equivalent
characterizations of a pure ideal. -/
@[stacks 04PS]
theorem tfae {R : Type u} [CommRing R] (I : Ideal R) :
    List.TFAE
      [ I.Pure
      , ∀ J : Ideal R, I ⊓ J = I * J
      , ∀ ⦃J : Ideal R⦄, J.FG → I ⊓ J = I * J
      , ∀ x : R, I ⊓ Ideal.span ({x} : Set R) = I * Ideal.span ({x} : Set R)
      , ∀ x : R, x ∈ I → ∃ y ∈ I, x = x * y
      , ∀ s : Finset R, (∀ x ∈ s, x ∈ I) → ∃ y ∈ I, ∀ x ∈ s, x = x * y
      , ∀ p : PrimeSpectrum R,
          Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) I = ⊥ ∨
            Ideal.map (algebraMap R (Localization.AtPrime p.asIdeal)) I = ⊤
      , Module.support R I = (PrimeSpectrum.zeroLocus (I : Set R))ᶜ
      , RingHom.ker (algebraMap R (Localization I.oneAdd)) = I
      , ∃ S : Submonoid R, Nonempty ((R ⧸ I) ≃ₐ[R] Localization S)
      , Nonempty ((R ⧸ I) ≃ₐ[R] Localization I.oneAdd)
      ] := sorry

end Ideal.Pure
