/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.FractionRing
public import ReasLib.RingTheory.Normal.Nagata.Dedekind
public import ReasLib.RingTheory.Regular.JRing.DimensionOne
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Dedekind J-2 Rings

@stack 07PJ

Characteristic-zero Dedekind domains form a canonical source of `J-2` rings.
-/

universe u v

namespace IsJ2Ring

/-- A Dedekind domain whose fraction field has characteristic zero is `J-2`. -/
@[stacks 07PJ "(6), characteristic-zero Dedekind domains"]
instance dedekindOfFractionRingCharZero (R : Type u) [CommRing R]
    [IsDedekindDomain R] [CharZero (FractionRing R)] : IsJ2Ring.{u, v} R := sorry

end IsJ2Ring
