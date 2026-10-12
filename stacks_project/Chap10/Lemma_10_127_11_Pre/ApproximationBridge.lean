/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap10.Lemma_10_127_11_Pre
public import stacks_project.Chap10.Lemma_10_127_9.ApproximationBridge
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.Tail.BaseChange
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Prime-localization transitions on approximation tails

@stack 00QX

The neutral approximation API owns restriction of base-change properties to a
cofinal tail.  This leaf keeps only the source-facing bridge needed by the
Chapter 10 module construction.
-/

@[expose] public section

universe u v

namespace DirectedLocalHomApproximation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- Lemma 10.127.13: prime-localization transition witnesses transfer to the
source-facing cofinal tail.  The underlying property transport is
`Hom.tail_baseChange_isLocalizationAtPrime`. -/
@[stacks 00QX "legacy approximation tail bridge"]
theorem tail_hasPrimeLocalizationTransitions
    (A : DirectedLocalHomApproximation f)
    (hA : A.HasPrimeLocalizationTransitions) (i₀ : A.Λ) :
    (A.tail i₀).HasPrimeLocalizationTransitions := sorry

end DirectedLocalHomApproximation

#check @DirectedLocalHomApproximation.tail_hasPrimeLocalizationTransitions
#print axioms DirectedLocalHomApproximation.tail_hasPrimeLocalizationTransitions
