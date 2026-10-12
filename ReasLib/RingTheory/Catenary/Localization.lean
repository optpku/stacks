/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Catenary.Universally

@[expose] public section

/-!
# Catenarity Under Localization

Localization stability is separate from the basic catenarity owners so that
finite-type and local applications can import this closure API directly.

@stack 00NJ
-/

universe u v

section

variable {R : Type u} [CommRing R]

/-- A localization of a catenary commutative ring is catenary. -/
@[stacks 00NJ]
instance localization_isCatenaryRing (M : Submonoid R) [IsCatenaryRing R] :
    IsCatenaryRing (Localization M) := sorry

/-- A localization of a universally catenary commutative ring is universally catenary. -/
@[stacks 00NJ]
instance localization_universallyCatenaryRing (M : Submonoid R)
    [UniversallyCatenaryRing.{u, v} R] : UniversallyCatenaryRing.{u, v} (Localization M) := sorry

end
