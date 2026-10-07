module

public import ReasLib.Algebra.Module.Injective.Hull
public import ReasLib.CategoryTheory.Limits.BinaryBiproduct.Indecomposable
public import ReasLib.RingTheory.Algebra.IsEpi.Injective
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.LocalRing.Basic

@[expose] public section

universe u v

/-- An indecomposable injective module is an injective hull of each of its nonzero submodules. -/
theorem Module.isInjectiveHull_subtype_of_indecomposable
    (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E]
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E))
    (N : Submodule R E) (hN : N ≠ ⊥) :
    (Submodule.subtype N).IsInjectiveHull := sorry

/-- Any two nonzero submodules of an indecomposable injective module have nonzero intersection. -/
theorem Module.inf_ne_bot_of_indecomposable_injective
    (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E]
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E))
    (M N : Submodule R E) (hM : M ≠ ⊥) (hN : N ≠ ⊥) :
    M ⊓ N ≠ ⊥ := sorry

/-- The endomorphism ring of an indecomposable injective module is local. -/
theorem Module.End.isLocalRing_of_indecomposable_injective
    (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E]
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E)) :
    IsLocalRing (Module.End R E) := sorry

/-- An endomorphism of an indecomposable injective module is a nonunit exactly when its
kernel is nonzero. -/
theorem Module.End.not_isUnit_iff_ker_ne_bot_of_indecomposable_injective
    (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E]
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E))
    (f : Module.End R E) :
    ¬ IsUnit f ↔ LinearMap.ker f ≠ ⊥ := sorry

/-- The ideal of scalars that annihilate a nonzero element of an indecomposable injective
module. -/
def Module.zeroDivisorIdeal
    (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E]
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E)) : Ideal R where
  carrier := {r | ∃ x : E, x ≠ 0 ∧ r • x = 0}
  zero_mem' := sorry
  add_mem' := sorry
  smul_mem' := sorry

/-- Membership in `Module.zeroDivisorIdeal` means annihilating a nonzero element. -/
theorem Module.mem_zeroDivisorIdeal_iff
    (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E]
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E)) (r : R) :
    r ∈ Module.zeroDivisorIdeal R E hE ↔ ∃ x : E, x ≠ 0 ∧ r • x = 0 := sorry

/-- The zero-divisor ideal of an indecomposable injective module is prime. -/
instance Module.instIsPrimeZeroDivisorIdeal
    (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E]
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E)) :
    (Module.zeroDivisorIdeal R E hE).IsPrime := sorry

/-- The canonical map from an indecomposable injective module to its localization at the
zero-divisor prime is bijective. -/
theorem Module.localizedAtZeroDivisorIdeal_bijective
    (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E]
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E)) :
    Function.Bijective
      (LocalizedModule.mkLinearMap (Module.zeroDivisorIdeal R E hE).primeCompl E) := sorry

/-- The localization of an indecomposable injective module at its zero-divisor prime is
injective over the localized ring. -/
instance Module.instInjectiveLocalizedAtZeroDivisorIdeal
    (R : Type u) (E : Type v) [CommRing R] [AddCommGroup E] [Module R E]
    [Module.Injective R E]
    (hE : CategoryTheory.Indecomposable (ModuleCat.of R E)) :
    Module.Injective
      (Localization.AtPrime (Module.zeroDivisorIdeal R E hE))
      (LocalizedModule.AtPrime (Module.zeroDivisorIdeal R E hE) E) := sorry
