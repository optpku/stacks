/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.StrictHenselization

@[expose] public section

/-!
# Composition with a Henselization

This leaf records the owner-level composition rule for a strict henselization
over a henselization.  It is independent of a selected separable closure or
of any source construction.

@stack 0BSL
-/

universe u v w

namespace IsStrictHenselizationOf

variable {R : Type u} {Rh : Type v} {Rsh : Type w}
variable [CommRing R] [IsLocalRing R]
variable [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable [CommRing Rsh] [Algebra Rh Rsh] [Algebra R Rsh] [IsScalarTower R Rh Rsh]

/-- Remark 10.155.4 (tag `0BSL`): a strict henselization over a henselization
of `R` is also a strict henselization of `R`. -/
@[stacks 0BSL "strict henselization composed with henselization"]
theorem of_henselization [IsStrictHenselizationOf Rh Rsh] :
    IsStrictHenselizationOf R Rsh := sorry

end IsStrictHenselizationOf
