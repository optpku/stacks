/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Nagata

@[expose] public section

/-!
# Nagata Dedekind Domains

This leaf provides the characteristic-zero Dedekind-domain case of the
Nagata condition.
-/

universe u

namespace NagataRing

/-- A Dedekind domain whose fraction field has characteristic zero is Nagata. -/
@[stacks 0335 "Dedekind-domain case"]
instance instOfDedekindDomainCharZero (R : Type u) [CommRing R]
    [IsDedekindDomain R] [CharZero (FractionRing R)] : NagataRing R := sorry

end NagataRing
