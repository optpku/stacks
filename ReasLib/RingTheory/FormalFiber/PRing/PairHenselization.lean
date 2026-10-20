module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.FormalFiber.FieldProperty.Laws
public import ReasLib.RingTheory.FormalFiber.PRing
public import ReasLib.RingTheory.Henselian.PairHenselization

@[expose] public section

/-!
# P-rings and Henselizations of Pairs

@stack 0BKA

The permanence theorem is stated for the intrinsic `IsPairHenselization` owner, independently of
any chosen categorical construction of the henselization.
-/

universe u

namespace IsPairHenselization

/-- A henselization of a pair over a `P`-ring is again a `P`-ring when `P` has the locality,
regular-ascent, faithfully-flat-descent, and separable-extension laws. -/
@[stacks 0BKA "pair henselizations of P-rings"]
theorem isPRing
    (P : FieldAlgebraProperty.{u, u}) [P.IsLocal] [P.RegularFiberAscent]
    [P.FaithfullyFlatDescent] [P.SeparableExtension]
    {B A : Type u} [CommRing B] [CommRing A] {J : Ideal B}
    [Algebra B A] {I : Ideal A} [IsPairHenselization B J A I]
    (hB : IsPRing P B) : IsPRing P A := sorry

end IsPairHenselization
