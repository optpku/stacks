module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import ReasLib.RingTheory.DiscreteValuationRing.Characterization
public import ReasLib.RingTheory.Normal.Ring
public import ReasLib.RingTheory.Valuation.Extension
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Weakly unramified height-one branches

This leaf owns the localized height-one branch predicate and the resulting descent of powers up
to units along flat local maps of Noetherian normal domains.

@stack 0ASI
-/

open Ideal IsLocalRing

universe u v

namespace HeightOneLocalization

/-- A height-one prime localization of a Noetherian normal domain is a discrete valuation ring. -/
@[stacks 0ASI "height-one localization of a Noetherian normal domain"]
theorem isDiscreteValuationRing
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsNormalRing R]
    (p : { p : PrimeSpectrum R // p.asIdeal.height = 1 }) :
    IsDiscreteValuationRing (Localization.AtPrime p.1.asIdeal) := sorry
-- Proof strategy: localize normality and Noetherianity at `p`, identify the
-- localized Krull dimension with `p.asIdeal.height = 1`, and apply the canonical
-- one-dimensional Noetherian normal local-domain characterization of DVRs.

/-- The canonical localization algebra attached to a height-one branch lying over a height-one
prime. It remains a named non-instance to avoid competing localization actions. -/
@[implicit_reducible, stacks 0ASI "canonical algebra on a height-one localization branch"]
noncomputable def algebra
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (p : { p : PrimeSpectrum A // p.asIdeal.height = 1 })
    (q : { q : PrimeSpectrum B // q.asIdeal.height = 1 })
    (hq : q.1.asIdeal.LiesOver p.1.asIdeal) :
    Algebra (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime q.1.asIdeal) :=
  letI : q.1.asIdeal.LiesOver p.1.asIdeal := hq
  Localization.AtPrime.algebraOfLiesOver p.1.asIdeal q.1.asIdeal

/-- A height-one branch of a flat map of Noetherian normal domains induces an extension of
valuation rings on the corresponding localizations. -/
@[stacks 0ASI "valuation-ring extension on a height-one branch"]
theorem isExtensionOfValuationRings
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsDomain A] [IsDomain B] [IsNormalRing A] [IsNormalRing B]
    [Module.Flat A B]
    (p : { p : PrimeSpectrum A // p.asIdeal.height = 1 })
    (q : { q : PrimeSpectrum B // q.asIdeal.height = 1 })
    (hq : q.1.asIdeal.LiesOver p.1.asIdeal) :
    letI : IsDiscreteValuationRing (Localization.AtPrime p.1.asIdeal) :=
      isDiscreteValuationRing p
    letI : IsDiscreteValuationRing (Localization.AtPrime q.1.asIdeal) :=
      isDiscreteValuationRing q
    letI : Algebra (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime q.1.asIdeal) :=
      algebra p q hq
    IsExtensionOfValuationRings
      (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime q.1.asIdeal) := sorry
-- Proof strategy: install the two DVR structures and `algebra p q hq`.
-- Localization of the flat map gives injectivity between the localized domains,
-- while the lying-over equality identifies maximal ideals and proves locality;
-- package these two facts as `IsExtensionOfValuationRings`.

/-- A height-one branch is weakly unramified when its canonical localized extension of valuation
rings has bijective value-group map. -/
@[stacks 0ASI "weakly unramified height-one branch"]
def IsWeaklyUnramifiedBranch
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsDomain A] [IsDomain B] [IsNormalRing A] [IsNormalRing B]
    [Module.Flat A B]
    (p : { p : PrimeSpectrum A // p.asIdeal.height = 1 })
    (q : { q : PrimeSpectrum B // q.asIdeal.height = 1 })
    (hq : q.1.asIdeal.LiesOver p.1.asIdeal) : Prop :=
  letI : IsDiscreteValuationRing (Localization.AtPrime p.1.asIdeal) :=
    isDiscreteValuationRing p
  letI : IsDiscreteValuationRing (Localization.AtPrime q.1.asIdeal) :=
    isDiscreteValuationRing q
  letI : Algebra (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime q.1.asIdeal) :=
    algebra p q hq
  letI : IsExtensionOfValuationRings
      (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime q.1.asIdeal) :=
    isExtensionOfValuationRings p q hq
  IsExtensionOfValuationRings.WeaklyUnramified
    (Localization.AtPrime p.1.asIdeal) (Localization.AtPrime q.1.asIdeal)

/-- Every height-one prime of the source has a weakly unramified height-one branch in the target.
-/
@[stacks 0ASI "existence of weakly unramified height-one branches"]
def HasWeaklyUnramifiedBranches
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsDomain A] [IsDomain B] [IsNormalRing A] [IsNormalRing B]
    [Module.Flat A B] : Prop :=
  ∀ p : { p : PrimeSpectrum A // p.asIdeal.height = 1 },
    ∃ q : { q : PrimeSpectrum B // q.asIdeal.height = 1 },
      ∃ hq : q.1.asIdeal.LiesOver p.1.asIdeal,
        IsWeaklyUnramifiedBranch p q hq

namespace HasWeaklyUnramifiedBranches

/-- Extract a weakly unramified target branch above a selected source height-one prime. -/
theorem existsBranch
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsDomain A] [IsDomain B] [IsNormalRing A] [IsNormalRing B]
    [Module.Flat A B]
    (h : HasWeaklyUnramifiedBranches A B)
    (p : { p : PrimeSpectrum A // p.asIdeal.height = 1 }) :
    ∃ q : { q : PrimeSpectrum B // q.asIdeal.height = 1 },
      ∃ hq : q.1.asIdeal.LiesOver p.1.asIdeal,
        IsWeaklyUnramifiedBranch p q hq := sorry
-- Proof strategy: unfold `HasWeaklyUnramifiedBranches` at `p` and return the
-- resulting branch, lying-over proof, and weak-unramified witness.

end HasWeaklyUnramifiedBranches

/-- Lemma 15.124.4 (0ASI): an `n`-th power up to a unit descends along a flat local map of
Noetherian local normal domains when every height-one prime has a weakly unramified branch. -/
@[stacks 0ASI "Lemma 15.124.4: descent of an n-th power up to a unit"]
theorem exists_unit_mul_pow_of_map_eq_unit_mul_pow
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsDomain A] [IsDomain B] [IsNormalRing A] [IsNormalRing B]
    [Module.Flat A B] [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)]
    {f : A} {h : B} {n : ℕ} (hn : 1 < n)
    (hbranch : HasWeaklyUnramifiedBranches A B)
    (hpow : ∃ w : Bˣ, algebraMap A B f = (w : B) * h ^ n) :
    ∃ (g : A) (u : Aˣ), f = (u : A) * g ^ n := sorry
-- Proof strategy: factor the divisor of `f` over the finite height-one support
-- of the normal Noetherian domain `A`.  For each height-one prime choose the
-- branch supplied by `hbranch`; weak unramifiedness identifies the two DVR
-- value groups, so the target `n`-th-power equation makes every source order
-- divisible by `n`.  Assemble the divided divisor into a principal ideal using
-- flat descent, choose its generator `g`, and use locality to show
-- `f / g ^ n` is a unit.

end HeightOneLocalization

end
