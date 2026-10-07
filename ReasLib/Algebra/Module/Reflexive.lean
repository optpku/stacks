module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Module.LocalizedModule.AtPrime
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Module

/-!
# Reflexive modules and depth

This leaf collects the reusable local-depth criteria for finite reflexive modules.  The primary
owners remain `Module.IsReflexive`, `moduleDepth`, and `Module.SerreConditionS`; the declarations
below connect those owners without introducing a second reflexive-module predicate.
-/

@[expose] public section

open Module
open LocalizedModule (AtPrime map)
open scoped ENat TensorProduct

universe u v w x

namespace LinearMap

/-- A map from a finite module over a Noetherian ring is bijective when at every prime it is
locally bijective, or the localized source has depth at least two and the prime is not associated
to the target. -/
@[stacks 0AV8 "Lemma 15.23.13"]
theorem bijective_of_localized_bijective_or_depth_ge_two_and_not_mem_associatedPrimes
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N)
    (h : ∀ p : PrimeSpectrum R,
      Function.Bijective (map p.asIdeal.primeCompl f) ∨
        ((2 : ℕ∞) ≤ moduleDepth (Localization.AtPrime p.asIdeal) (AtPrime p.asIdeal M) ∧
          p.asIdeal ∉ associatedPrimes R N)) :
    Function.Bijective f := sorry

/-- A linear map from a finite module to a torsion-free module is bijective when it is locally
bijective at every prime where the source does not already have depth at least two. -/
@[stacks 0AV9 "local depth criterion for bijectivity"]
theorem bijective_of_localized_bijective_or_depth_ge_two
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {N : Type w} [AddCommGroup N] [Module R N] [Module.IsTorsionFree R N]
    (f : M →ₗ[R] N)
    (h : ∀ p : PrimeSpectrum R,
      Function.Bijective (map p.asIdeal.primeCompl f) ∨
        (2 : ℕ∞) ≤ moduleDepth (Localization.AtPrime p.asIdeal) (AtPrime p.asIdeal M)) :
    Function.Bijective f := sorry

end LinearMap

namespace Module.Dual

/-- For a finite module over a domain, the kernel of the canonical evaluation map to the double
dual is torsion. -/
@[stacks 0AV0 "Lemma 15.23.2 (2), kernel clause"]
theorem eval_ker_isTorsion
    {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsTorsion R (eval R M).ker := sorry

/-- For a finite module over a domain, the cokernel of the canonical evaluation map to the double
dual is torsion. -/
@[stacks 0AV0 "Lemma 15.23.2 (2), cokernel clause"]
theorem eval_cokernel_isTorsion
    {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsTorsion R (Dual R (Dual R M) ⧸ (eval R M).range) := sorry

/-- For a finite module over a domain, the canonical evaluation map to the double dual is
injective exactly when the module is torsion-free. -/
@[stacks 0AV0 "Lemma 15.23.2 (3)"]
theorem eval_injective_iff_isTorsionFree
    {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Injective (eval R M) ↔ IsTorsionFree R M := sorry

/-- Over a principal ideal domain, the double-dual evaluation map of a finite module is
surjective. -/
theorem eval_surjective_of_isPrincipalIdealRing
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Surjective (eval R M) := sorry

/-- Over a discrete valuation ring, the double-dual evaluation map of a finite module is
surjective. -/
@[stacks 0B36 "Lemma 15.23.3"]
theorem eval_surjective_of_isDiscreteValuationRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Function.Surjective (eval R M) := sorry

end Module.Dual

namespace Module.IsReflexive

/-- A finite reflexive module remains reflexive after flat base change between Noetherian domains. -/
@[stacks 0EB9 "flat base change preserves reflexivity"]
theorem baseChange_of_flat
    {R : Type u} {R' : Type v} {M : Type w}
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing R'] [IsDomain R'] [Algebra R R'] [Flat R R']
    [AddCommGroup M] [Module R M] [Module.Finite R M] [IsReflexive R M] :
    IsReflexive R' (R' ⊗[R] M) := sorry

/-- A finitely presented module into a finite reflexive module has reflexive linear-map module. -/
@[stacks 0AV3 "reflexivity of a finite Hom module"]
theorem linearMap_of_finitePresentation
    {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} {N : Type w}
    [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [IsReflexive R N] :
    IsReflexive R (M →ₗ[R] N) := sorry

/-- Prime-local reflexivity is equivalent to bijectivity of the localized double-dual evaluation
map for a finitely presented module. -/
theorem atPrime_iff_bijective_eval
    {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    (P : Ideal R) [P.IsPrime] :
    IsReflexive (Localization.AtPrime P) (AtPrime P M) ↔
      Function.Bijective (LocalizedModule.map P.primeCompl (Module.Dual.eval R M)) := sorry

/-- A finite module over a Noetherian domain is reflexive exactly when all of its prime
localizations are reflexive, equivalently when all maximal localizations are reflexive. -/
@[stacks 0AV1 "Lemma 15.23.4"]
theorem localization_tfae
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    List.TFAE
      [ IsReflexive R M
      , ∀ (P : Ideal R) [P.IsPrime],
          IsReflexive (Localization.AtPrime P) (AtPrime P M)
      , ∀ (P : Ideal R) [P.IsMaximal],
          IsReflexive (Localization.AtPrime P) (AtPrime P M) ] := sorry

/-- Reflexivity descends to the source of an exact pair when the middle module is finite and
reflexive and the represented quotient is torsion-free. -/
theorem of_exact_of_range_torsionFree
    {R : Type u} [CommRing R] [IsDomain R]
    {M : Type v} {M' : Type w} {M'' : Type x}
    [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [AddCommGroup M''] [Module R M'']
    {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hfg : Function.Exact f g) (hf : Function.Injective f)
    [IsReflexive R M'] [IsTorsionFree R (LinearMap.range g)] :
    IsReflexive R M := sorry

/-- In an exact sequence of finite modules over a Noetherian domain, a reflexive middle term and
torsion-free target force the source to be reflexive. -/
@[stacks 0EB8 "Lemma 15.23.5"]
theorem of_exact_of_torsionFree
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {M : Type v} {M' : Type w} {M'' : Type x}
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M']
    [AddCommGroup M''] [Module R M''] [Module.Finite R M'']
    {f : M →ₗ[R] M'} {g : M' →ₗ[R] M''}
    (hfg : Function.Exact f g) (hf : Function.Injective f)
    [IsReflexive R M'] [IsTorsionFree R M''] :
    IsReflexive R M := sorry

/-- A finite module over a Noetherian domain is reflexive exactly when it embeds in a finite free
module with torsion-free cokernel. -/
@[stacks 0AV2 "Lemma 15.23.6"]
theorem iff_exists_fin_free_quotient_torsionFree
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsReflexive R M ↔
      ∃ n : ℕ, ∃ f : M →ₗ[R] (Fin n → R),
        Function.Injective f ∧ IsTorsionFree R ((Fin n → R) ⧸ LinearMap.range f) := sorry

/-- A finite module over a Noetherian domain is reflexive exactly when every prime localization is
reflexive or has depth at least two. -/
@[stacks 0AVA "prime-local reflexivity or depth criterion"]
theorem iff_forall_localization_or_depth_ge_two
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsReflexive R M ↔
      ∀ p : PrimeSpectrum R,
        IsReflexive (Localization.AtPrime p.asIdeal) (AtPrime p.asIdeal M) ∨
          (2 : ℕ∞) ≤ moduleDepth (Localization.AtPrime p.asIdeal) (AtPrime p.asIdeal M) := sorry

/-- A finite reflexive module has localized depth at least two wherever the localized ring does. -/
@[stacks 0EBA "localized depth of a reflexive module"]
theorem moduleDepth_localizationAtPrime_ge_two
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [IsReflexive R M]
    (p : PrimeSpectrum R)
    (hp : (2 : ℕ∞) ≤ moduleDepth (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal)) :
    (2 : ℕ∞) ≤ moduleDepth (Localization.AtPrime p.asIdeal) (AtPrime p.asIdeal M) := sorry

/-- A finite reflexive module over an `(S₂)` ring canonically satisfies module `(S₂)`. -/
@[stacks 0EBA "reflexive modules satisfy Serre S2"]
instance instSerreConditionSTwo
    {R : Type u} [CommRing R] [R ⊧ (S₂)]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] [IsReflexive R M] :
    SerreConditionS R M 2 := sorry

end Module.IsReflexive
