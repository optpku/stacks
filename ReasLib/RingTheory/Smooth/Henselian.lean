/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Smooth algebras over henselian pairs

@stack 0H74

This file provides the canonical lifting interface for maps from a smooth
algebra to the quotient of a henselian pair.
-/

universe u v w

namespace Algebra.Smooth

/-- Stacks 0H74: a smooth `R`-algebra lifts maps across the quotient of every henselian pair
`(A, I)`. -/
@[stacks 0H74]
theorem exists_lift_of_henselian
    {R : Type u} {S : Type v} {A : Type w}
    [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra R A] [Algebra.Smooth R S]
    (I : Ideal A) [HenselianRing A I] (f : S →ₐ[R] A ⧸ I) :
    ∃ f' : S →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp f' = f := sorry

end Algebra.Smooth
