/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Catenary.Universally

@[expose] public section

/-!
# Catenarity Under Quotients

@stack 00NK

The quotient instances are global because they are canonical closure facts for
the two catenarity owners.
-/

universe u v

section

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- Lemma 10.105.7 (1): a quotient of a catenary ring is catenary. -/
@[stacks 00NK]
instance quotient_catenaryRing [IsCatenaryRing R] : IsCatenaryRing (R ⧸ I) := sorry

/-- Lemma 10.105.7 (2): a quotient of a universally catenary ring is universally catenary. -/
@[stacks 00NK]
instance quotient_universallyCatenaryRing [UniversallyCatenaryRing.{u, v} R] :
    UniversallyCatenaryRing.{u, v} (R ⧸ I) := sorry

end
