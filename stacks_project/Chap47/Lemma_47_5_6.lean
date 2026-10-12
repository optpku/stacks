/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Injective.Indecomposable
import StacksCheckRecall

@[expose] public section

universe u v

/- Lemma 47.5.6: The ideal of scalars that annihilate a nonzero element of an
indecomposable injective module. -/
@[stacks 08Y7] #check (Module.zeroDivisorIdeal :
  ∀ (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E],
    CategoryTheory.Indecomposable (ModuleCat.of R E) → Ideal R)

/- Lemma 47.5.6: Membership in the zero-divisor ideal means annihilating a
nonzero element. -/
@[stacks 08Y7] #check (Module.mem_zeroDivisorIdeal_iff :
  ∀ (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E],
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E)) → ∀ r : R,
      r ∈ Module.zeroDivisorIdeal R E hE ↔ ∃ x : E, x ≠ 0 ∧ r • x = 0)

/- Lemma 47.5.6: An indecomposable injective module is an injective hull of each
of its nonzero submodules. -/
@[stacks 08Y7] #check (Module.isInjectiveHull_subtype_of_indecomposable :
  ∀ (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E],
    CategoryTheory.Indecomposable (ModuleCat.of R E) →
      ∀ (N : Submodule R E), N ≠ ⊥ → (Submodule.subtype N).IsInjectiveHull)

/- Lemma 47.5.6: Any two nonzero submodules of an indecomposable injective
module have nonzero intersection. -/
@[stacks 08Y7] #check (Module.inf_ne_bot_of_indecomposable_injective :
  ∀ (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E],
    CategoryTheory.Indecomposable (ModuleCat.of R E) →
      ∀ (M N : Submodule R E), M ≠ ⊥ → N ≠ ⊥ → M ⊓ N ≠ ⊥)

/- Lemma 47.5.6: The endomorphism ring of an indecomposable injective module is
local. -/
@[stacks 08Y7] #check (Module.End.isLocalRing_of_indecomposable_injective :
  ∀ (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E],
    CategoryTheory.Indecomposable (ModuleCat.of R E) →
      IsLocalRing (Module.End R E))

/- Lemma 47.5.6: An endomorphism is a nonunit exactly when its kernel is
nonzero. -/
@[stacks 08Y7] #check (Module.End.not_isUnit_iff_ker_ne_bot_of_indecomposable_injective :
  ∀ (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E],
    CategoryTheory.Indecomposable (ModuleCat.of R E) → ∀ f : Module.End R E,
      ¬ IsUnit f ↔ LinearMap.ker f ≠ ⊥)

/- Lemma 47.5.6: The zero-divisor ideal of an indecomposable injective module is
prime. -/
@[stacks 08Y7] #check (Module.instIsPrimeZeroDivisorIdeal :
  ∀ (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E],
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E)) →
      (Module.zeroDivisorIdeal R E hE).IsPrime)

/- Lemma 47.5.6: The canonical map to the localization at the zero-divisor
prime is bijective. -/
@[stacks 08Y7] #check (Module.localizedAtZeroDivisorIdeal_bijective :
  ∀ (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E],
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E)) →
      Function.Bijective
        (LocalizedModule.mkLinearMap (Module.zeroDivisorIdeal R E hE).primeCompl E))

/- Lemma 47.5.6: The localization at the zero-divisor prime is injective over
the localized ring. -/
@[stacks 08Y7] #check (Module.instInjectiveLocalizedAtZeroDivisorIdeal :
  ∀ (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E],
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E)) →
      Module.Injective
        (Localization.AtPrime (Module.zeroDivisorIdeal R E hE))
        (LocalizedModule.AtPrime (Module.zeroDivisorIdeal R E hE) E))
