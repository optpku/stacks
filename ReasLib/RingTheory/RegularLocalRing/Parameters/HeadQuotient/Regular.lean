/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.Quotient.Head
public import ReasLib.RingTheory.RegularLocalRing.Parameters.HeadQuotient
public import ReasLib.RingTheory.RegularLocalRing.Parameters.Properties

@[expose] public section

/-!
# Regular Head Quotients of Parameter Systems

This leaf records the regular-local consequences of quotienting a regular
system of parameters by its first entry.  The generic quotient construction
is owned by `Ideal.Quotient.Head`; the local maximal-ideal tail is owned by
`Parameters.HeadQuotient`, while regular-sequence and dimension APIs remain
in their separate leaves.
-/

universe u

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

namespace IsRegularSystemOfParameters

/-- The tail of a regular system of parameters is a regular system after
quotienting by the head parameter. -/
@[stacks 00NQ "regular system after head quotient"]
theorem headQuotientTail {d : ℕ} {x : Fin (d + 1) → maximalIdeal R}
    (hx : IsRegularSystemOfParameters x) :
    IsRegularSystemOfParameters (IsLocalRing.HeadQuotient.tail x) := sorry

/-- Quotienting a regular system of parameters by its head gives a regular
local ring. -/
@[stacks 00NQ "regular local head quotient"]
theorem headQuotient_isRegularLocalRing {d : ℕ} {x : Fin (d + 1) → maximalIdeal R}
    (hx : IsRegularSystemOfParameters x) :
    IsRegularLocalRing (R ⧸ Ideal.headIdeal (fun i ↦ (x i : R))) := sorry

/-- The head quotient of a regular system with `d + 1` entries has Krull
dimension `d`. -/
@[stacks 00NQ "head quotient Krull dimension"]
theorem ringKrullDim_headQuotient {d : ℕ} {x : Fin (d + 1) → maximalIdeal R}
    (hx : IsRegularSystemOfParameters x) :
    ringKrullDim (R ⧸ Ideal.headIdeal (fun i ↦ (x i : R))) = d := sorry

end IsRegularSystemOfParameters

end IsLocalRing
