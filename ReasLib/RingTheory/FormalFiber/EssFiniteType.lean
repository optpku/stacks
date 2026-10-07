module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.FormalFiber.Maximal
public import ReasLib.RingTheory.FormalFiber.QuasiFinite

@[expose] public section

/-!
# Essentially finite type extensions of P-rings

@stack 0BIV

This is the reusable ring-level permanence theorem assembled from the four independent
formal-fiber laws it actually needs.
-/

universe u

namespace IsPRing

/-- An essentially finite type algebra over a `P`-ring is a `P`-ring when `P` has base-change,
locality, regular-ascent, and faithfully-flat-descent laws. -/
@[stacks 0BIV "essentially finite type extension of a P-ring"]
theorem of_essFiniteType (P : FieldAlgebraProperty.{u, u})
    [P.EssFiniteTypeBaseChange] [P.IsLocal]
    [P.RegularFiberAscent] [P.FaithfullyFlatDescent]
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] (hR : IsPRing P R) :
    IsPRing P S := sorry

end IsPRing
