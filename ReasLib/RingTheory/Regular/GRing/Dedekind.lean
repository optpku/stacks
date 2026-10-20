/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.Localization.FractionRing
public import ReasLib.RingTheory.Regular.GRing
import Mathlib.Tactic.CrossRefAttribute

/-!
# Dedekind G-rings

@stack 07PX

This leaf is independent of the alternative formal-fiber characterization of G-rings.
-/

@[expose] public section

universe u

namespace IsGRing

/-- A Dedekind domain whose fraction field has characteristic zero is a G-ring. -/
@[stacks 07PX "characteristic-zero Dedekind domains are G-rings"]
instance dedekindOfFractionRingCharZero (R : Type u) [CommRing R]
    [IsDedekindDomain R] [CharZero (FractionRing R)] : IsGRing R := sorry

end IsGRing
