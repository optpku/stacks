/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Dimension at most one from Krull dimension

This leaf owns the elementary dimension-one implication for domains.  It is
independent of locality, integral closures, and valuation-theoretic applications.
-/

@[expose] public section

universe u

namespace Ring

/-- A domain of ring Krull dimension one has dimension at most one. -/
@[stacks 09IG "dimension at most one from Krull dimension one"]
theorem dimensionLEOne_of_ringKrullDim_eq_one
    {R : Type u} [CommRing R] [IsDomain R]
    (hdim : ringKrullDim R = 1) :
    Ring.DimensionLEOne R := sorry

end Ring
