module

public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Regular.GRing

@[expose] public section

/-!
# Essentially Finite Type Extensions of G-Rings

@stack 07PV
@stack 07PX

This leaf owns the cross-universe permanence API for G-rings.  The results are
explicit theorems rather than global instances because the algebra base cannot
be recovered canonically from the target ring.
-/

universe u v

namespace IsGRing

/-- An essentially finite type algebra over a G-ring is a G-ring. -/
@[stacks 07PV "essentially finite type extension of a G-ring"]
theorem of_essFiniteType (R : Type u) {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] [IsGRing R]
    [Algebra.EssFiniteType R S] : IsGRing S := sorry

/-- A finite type algebra over a G-ring is a G-ring. -/
@[stacks 07PX "finite type extension of a G-ring"]
theorem of_finiteType (R : Type u) {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S] [IsGRing R]
    [Algebra.FiniteType R S] : IsGRing S := sorry

end IsGRing
