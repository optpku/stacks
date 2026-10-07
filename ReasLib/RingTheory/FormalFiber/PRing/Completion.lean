module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.FormalFiber.FieldProperty.Laws
public import ReasLib.RingTheory.FormalFiber.PRing

@[expose] public section

/-!
# P-rings and Adic Completion

@stack 0BK9

The fibers of an arbitrary adic completion of a `P`-ring inherit `P` using only locality and
faithfully-flat descent.  No separate Noetherian hypothesis is exposed because it is part of the
`IsPRing` owner.
-/

universe u

namespace IsPRing

/-- Every fiber of an adic completion of a `P`-ring has property `P`. -/
@[stacks 0BK9 "adic-completion fibers of a P-ring"]
theorem adicCompletionFiber
    {P : FieldAlgebraProperty.{u, u}} [P.IsLocal] [P.FaithfullyFlatDescent]
    {A : Type u} [CommRing A] (hA : IsPRing P A) (I : Ideal A) (p : PrimeSpectrum A) :
    P p.asIdeal.ResidueField (p.asIdeal.Fiber (AdicCompletion I A)) := sorry

end IsPRing
