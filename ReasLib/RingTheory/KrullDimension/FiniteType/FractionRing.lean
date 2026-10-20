/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.KrullDimension.FiniteType
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Dimension and fraction-field transcendence degree

This leaf gives the fraction-field form of the dimension theorem for a
finite-type domain over a field, together with its maximal-localization form.
-/

@[expose] public section

universe u v

namespace Algebra.FiniteType

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [IsDomain S] [Algebra k S]
  [Algebra.FiniteType k S]

/-- The Krull dimension of a finite-type domain over a field is the
transcendence degree of its fraction field. -/
@[stacks 00P0 "(1), global fraction-field dimension"]
theorem ringKrullDim_eq_trdeg_fractionRing :
    ringKrullDim S = Cardinal.toNat (Algebra.trdeg k (FractionRing S)) := sorry

/-- Every maximal localization of a finite-type domain has dimension equal to
the transcendence degree of its fraction field. -/
@[stacks 00P0 "(2), maximal-local dimension"]
theorem ringKrullDim_localizationAtMaximal_eq_trdeg_fractionRing
    (m : MaximalSpectrum S) :
    ringKrullDim (Localization.AtPrime m.asIdeal) =
      Cardinal.toNat (Algebra.trdeg k (FractionRing S)) := sorry

end Algebra.FiniteType
