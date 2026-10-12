/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Ring
public import ReasLib.RingTheory.Smooth.Regularity

/-!
# Normality of Smooth Algebras

This leaf owns normality ascent along smooth algebra maps.  Its proof may use
regularity of smooth field fibers, but consumers only need the resulting
normal-base statement.
-/

@[expose] public section

namespace Algebra.Smooth

universe u v

/-- A smooth algebra over a normal ring is a normal ring. -/
@[stacks 033C "normality ascends along smooth algebras"]
theorem isNormalRing_of_normal
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] [IsNormalRing R] :
    IsNormalRing S := sorry

end Algebra.Smooth
