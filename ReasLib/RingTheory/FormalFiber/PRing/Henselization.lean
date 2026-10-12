/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.FormalFiber.FieldProperty.Laws
public import ReasLib.RingTheory.FormalFiber.PRing
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.StrictHenselization

@[expose] public section

/-!
# P-rings under Henselization

@stack 0C36

These statements use the intrinsic owners for arbitrary chosen henselizations and strict
henselizations.  The target stays in the source universe because the current generic `P`-ring
machine is same-universe.
-/

universe u

namespace IsHenselizationOf

/-- A henselization of a local `P`-ring is a `P`-ring. -/
@[stacks 0C36 "henselizations of P-rings"]
theorem isPRing
    (P : FieldAlgebraProperty.{u, u}) [P.IsLocal] [P.RegularFiberAscent]
    [P.FaithfullyFlatDescent] [P.SeparableExtension]
    {R Rh : Type u} [CommRing R] [IsLocalRing R] [CommRing Rh] [Algebra R Rh]
    [IsHenselizationOf R Rh] (hR : IsPRing P R) : IsPRing P Rh := sorry

end IsHenselizationOf

namespace IsStrictHenselizationOf

/-- A strict henselization of a local `P`-ring is a `P`-ring. -/
@[stacks 0C36 "strict henselizations of P-rings"]
theorem isPRing
    (P : FieldAlgebraProperty.{u, u}) [P.IsLocal] [P.RegularFiberAscent]
    [P.FaithfullyFlatDescent] [P.SeparableExtension]
    {R Rsh : Type u} [CommRing R] [IsLocalRing R] [CommRing Rsh] [Algebra R Rsh]
    [IsStrictHenselizationOf R Rsh] (hR : IsPRing P R) : IsPRing P Rsh := sorry

end IsStrictHenselizationOf
