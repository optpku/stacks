/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import ReasLib.Algebra.Module.Reflexive.GenericFiber
public import ReasLib.RingTheory.Normal.Serre

/-!
# Reflexive modules over normal domains

This leaf owns the height-one localization intersection and the resulting characterizations of
finite reflexive modules over Noetherian normal domains.

@stack 0AVB
@stack 0AVC
@stack 0BM4
-/

@[expose] public section

open Module
open LocalizedModule (liftOfLE mkLinearMap)
open scoped nonZeroDivisors

universe u v

namespace Module

/-- The intersection of the height-one localizations of a module inside its generic
localization. -/
@[stacks 0AVB "height-one localization intersection", stacks 0AVC "height-one localization intersection"]
noncomputable abbrev heightOneLocalizationIntersection
    (R : Type u) (M : Type v)
    [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M] :
    Submodule R (LocalizedModule R⁰ M) :=
  ⨅ p : { p : PrimeSpectrum R // p.asIdeal.height = 1 },
    LinearMap.range
      (liftOfLE p.1.asIdeal.primeCompl R⁰
        (Ideal.primeCompl_le_nonZeroDivisors p.1.asIdeal))

end Module

namespace Module.IsReflexive

/-- Lemma 15.23.18: for a finite module over a Noetherian normal domain, reflexivity is equivalent
to torsion-freeness plus `(S₂)`, and to equality with the height-one localization intersection. -/
@[stacks 0AVB "Lemma 15.23.18"]
theorem normalDomain_tfae
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    List.TFAE
      [ IsReflexive R M
      , IsTorsionFree R M ∧ SerreConditionS R M 2
      , IsTorsionFree R M ∧
          LinearMap.range (mkLinearMap R⁰ M) =
            Module.heightOneLocalizationIntersection R M ] := sorry

end Module.IsReflexive

namespace Module.Dual

/-- Lemma 15.23.19: the image of the reflexive hull in the generic localization of the
torsion-free quotient is its height-one localization intersection. -/
@[stacks 0AVC "Lemma 15.23.19"]
theorem range_toTorsionQuotientGenericLocalization_eq_heightOneLocalizationIntersection
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (heval : Function.Bijective (LocalizedModule.map R⁰ (eval R M)))
    (hquot : Function.Bijective
      (LocalizedModule.map R⁰ (Submodule.torsion R M).mkQ)) :
    (toTorsionQuotientGenericLocalizationOf heval hquot).range =
      Module.heightOneLocalizationIntersection R (M ⧸ Submodule.torsion R M) := sorry

end Module.Dual

namespace integralClosure

/-- Lemma 15.23.20: a finite integral closure in a finite fraction-field extension is reflexive
over a Noetherian normal domain. -/
@[stacks 0BM4 "Lemma 15.23.20"]
instance instIsReflexiveOfFinite
    {A : Type u} {L : Type v}
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Field L] [Algebra A L] [Algebra (FractionRing A) L]
    [IsScalarTower A (FractionRing A) L] [FiniteDimensional (FractionRing A) L]
    [Module.Finite A (integralClosure A L)] :
    Module.IsReflexive A (integralClosure A L) := sorry

end integralClosure
