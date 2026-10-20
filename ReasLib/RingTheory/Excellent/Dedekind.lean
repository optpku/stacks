module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Catenary.Dedekind
public import ReasLib.RingTheory.Excellent
public import ReasLib.RingTheory.Regular.GRing.Dedekind
public import ReasLib.RingTheory.Regular.JRing.Dedekind

@[expose] public section

/-!
# Excellent Dedekind Domains

@stack 07QW
-/

universe u v

namespace IsExcellentRing

/-- A Dedekind domain with characteristic-zero fraction field is excellent. -/
@[stacks 07QW "characteristic-zero Dedekind domains are excellent"]
instance dedekindOfFractionRingCharZero
    (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero (FractionRing R)] :
    IsExcellentRing.{u, v} R := sorry

/-- The polynomial ring over a finite prime field is excellent. -/
instance polynomialZMod (p : ℕ) [Fact p.Prime] :
    IsExcellentRing (Polynomial (ZMod p)) := sorry

end IsExcellentRing
