/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.FormalFiber.GRing
public import ReasLib.RingTheory.FormalFiber.PRing.Henselization

@[expose] public section

/-!
# G-rings under Henselization

@stack 07QR

These theorems specialize the reusable `P`-ring permanence API to geometrically regular formal
fibers.  The source ring is not determined by the target ring alone, so the source `G`-ring fact
remains an explicit argument instead of becoming a hidden-base instance.
-/

universe u

namespace IsHenselizationOf

/-- A henselization of a local `G`-ring is a `G`-ring. -/
@[stacks 07QR "(1), henselizations of G-rings"]
theorem isGRing
    {R Rh : Type u} [CommRing R] [IsLocalRing R] [CommRing Rh] [Algebra R Rh]
    [IsHenselizationOf R Rh] (hR : IsGRing R) : IsGRing Rh := sorry

end IsHenselizationOf

namespace IsStrictHenselizationOf

/-- A strict henselization of a local `G`-ring is a `G`-ring. -/
@[stacks 07QR "(2), strict henselizations of G-rings"]
theorem isGRing
    {R Rsh : Type u} [CommRing R] [IsLocalRing R] [CommRing Rsh] [Algebra R Rsh]
    [IsStrictHenselizationOf R Rsh] (hR : IsGRing R) : IsGRing Rsh := sorry

end IsStrictHenselizationOf
