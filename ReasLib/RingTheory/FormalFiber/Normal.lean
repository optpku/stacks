/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Flat.Fiber.Normal
public import ReasLib.RingTheory.FormalFiber.PRing
public import ReasLib.RingTheory.Normal.Ring

@[expose] public section

/-!
# Normal Formal Fibers

@stack 0C23

This file gives ordinary normality as a field-algebra property and records the completion theorem
in terms of that reusable formal-fiber predicate.
-/

open IsLocalRing

universe u v

namespace FieldAlgebraProperty

/-- Ordinary normality, viewed as a property of algebras over fields. -/
@[stacks 0C23 "normal field-algebra property"]
abbrev normal : FieldAlgebraProperty.{u, v} :=
  fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦ IsNormalRing A

end FieldAlgebraProperty

namespace IsNormalRing

/-- A normal Noetherian local ring with normal formal fibers has normal maximal-ideal
completion. -/
@[stacks 0C23 "normality of the completion"]
theorem adicCompletion_of_formalFibers
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalRing A]
    (h_formal : FieldAlgebraProperty.normal.HoldsOnFormalFibers A) :
    IsNormalRing (AdicCompletion (maximalIdeal A) A) := sorry

end IsNormalRing
