/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Henselian.FaithfullyFlat
public import ReasLib.RingTheory.KrullDimension.Etale
import Mathlib.Tactic.CrossRefAttribute

/-!
# Krull dimension and henselization

Henselization and strict henselization preserve the Krull dimension of a
local ring.

@stack 06LK
-/

@[expose] public section

universe u v

namespace IsHenselizationOf

variable {R : Type u} {S : Type v}
variable [CommRing R] [IsLocalRing R]
variable [CommRing S] [Algebra R S] [IsHenselizationOf R S]

/-- Lemma 15.45.7 (1) (06LK): a local ring and a henselization have
the same Krull dimension. -/
@[stacks 06LK "Krull dimension of a Henselization"]
theorem ringKrullDim_eq : ringKrullDim R = ringKrullDim S := sorry

end IsHenselizationOf

namespace IsStrictHenselizationOf

variable {R : Type u} {S : Type v}
variable [CommRing R] [IsLocalRing R]
variable [CommRing S] [Algebra R S] [IsStrictHenselizationOf R S]

/-- Lemma 15.45.7 (2) (06LK): a local ring and a strict henselization
have the same Krull dimension. -/
@[stacks 06LK "Krull dimension of a strict Henselization"]
theorem ringKrullDim_eq : ringKrullDim R = ringKrullDim S := sorry

end IsStrictHenselizationOf
