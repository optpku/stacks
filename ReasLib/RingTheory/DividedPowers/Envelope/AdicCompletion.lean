/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.Envelope
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Nilpotent.Defs

@[expose] public section

universe u

open scoped Pointwise

/-- Nilpotence of an integer in the presented quotient forces its corresponding
power to lie in the distinguished ideal of the divided-power envelope. -/
theorem DividedPowerEnvelope.primePowLeIdeal
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    {I : Ideal A} (gamma : DividedPowers I) (f : A →+* B)
    {J : Ideal B} (hIJ : Ideal.map f I ≤ J)
    (E : DividedPowerEnvelope I gamma f J hIJ) (q : B →+* C)
    (hJ : J = RingHom.ker q) (p : ℕ) (hpnil : IsNilpotent (p : C)) :
    Ideal.span {(p : E.D)} ^ nilpotencyClass (p : C) ≤ E.D.ideal := sorry

/-- A nilpotent prime-power element of a quotient forces the corresponding power
of the completed envelope to lie in the image of its distinguished ideal. -/
theorem DividedPowerEnvelope.primePowLeCompletionIdeal
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    {I : Ideal A} (gamma : DividedPowers I) (f : A →+* B)
    {J : Ideal B} (hIJ : Ideal.map f I ≤ J)
    (E : DividedPowerEnvelope I gamma f J hIJ) (q : B →+* C)
    (hJ : J = RingHom.ker q) (p : ℕ) (hpnil : IsNilpotent (p : C)) :
    Ideal.span {(p : AdicCompletion (Ideal.span {(p : E.D)}) E.D)} ^
        nilpotencyClass (p : C) ≤
      Ideal.map (algebraMap E.D (AdicCompletion (Ideal.span {(p : E.D)}) E.D)) E.D.ideal := sorry
