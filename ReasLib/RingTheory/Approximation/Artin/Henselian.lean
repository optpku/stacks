/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.Congruence
public import ReasLib.RingTheory.Henselian.PairHenselization.GRing
public import ReasLib.RingTheory.MvPolynomial.Solution
import ReasLib.RingTheory.Smooth.Henselian

@[expose] public section

/-!
# Artin approximation for henselian pairs

The core approximation theorem assumes regularity of the relevant adic
completion map.  G-rings and pair henselizations enter only through reusable
bridges supplying that regularity.
-/

open MvPolynomial

universe u v w x

namespace HenselianRing.ArtinApproximation

/-- Lemma 16.14.1, regular-completion core: for a Noetherian henselian pair
with regular completion map, a formal solution of a finite polynomial system
can be approximated by an exact solution modulo every positive power of the
ideal. -/
@[stacks 0AH5]
theorem nonempty
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    [HenselianRing A I]
    [hreg : (algebraMap A (AdicCompletion I A)).Regular]
    {sigma : Type w} {iota : Type x} [Finite sigma] [Finite iota]
    (f : iota → MvPolynomial sigma A) (aHat : sigma → AdicCompletion I A)
    (hroots : IsSolution f aHat) (N : ℕ+) :
    Nonempty (SolutionApproximation f aHat
      (Algebra.ofId A (AdicCompletion I A))
      (AdicCompletion.extendedIdealPow I N)) := sorry

/-- Lemma 16.14.1, G-ring branch: Artin approximation for every henselian
ideal. -/
@[stacks 0AH5 "G-ring branch"]
theorem nonempty_of_isGRing
    {A : Type u} [CommRing A] [IsGRing A] (I : Ideal A)
    [HenselianRing A I]
    {sigma : Type w} {iota : Type x} [Finite sigma] [Finite iota]
    (f : iota → MvPolynomial sigma A) (aHat : sigma → AdicCompletion I A)
    (hroots : IsSolution f aHat) (N : ℕ+) :
    Nonempty (SolutionApproximation f aHat
      (Algebra.ofId A (AdicCompletion I A))
      (AdicCompletion.extendedIdealPow I N)) := sorry

/-- Lemma 16.14.1, pair-henselization branch: Artin approximation also holds
for a pair henselization of a Noetherian G-ring. -/
@[stacks 0AH5 "pair henselization branch"]
theorem nonempty_of_pair
    {B : Type v} [CommRing B] [IsGRing B] (J : Ideal B)
    {A : Type u} [CommRing A] [Algebra B A] (I : Ideal A)
    [IsPairHenselization B J A I]
    {sigma : Type w} {iota : Type x} [Finite sigma] [Finite iota]
    (f : iota → MvPolynomial sigma A) (aHat : sigma → AdicCompletion I A)
    (hroots : IsSolution f aHat) (N : ℕ+) :
    Nonempty (SolutionApproximation f aHat
      (Algebra.ofId A (AdicCompletion I A))
      (AdicCompletion.extendedIdealPow I N)) := sorry

end HenselianRing.ArtinApproximation
