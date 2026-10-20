module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Nagata

@[expose] public section

/-!
# Finite Extensions of Japanese Domains

This module records descent of the `N-1` and `N-2` conditions along injective
module-finite maps of Noetherian domains.
-/

universe u v

section

variable {R : Type u} {S : Type v}

namespace IsN1Ring

/-- Lemma 10.161.7 (1), tag `032K`: an injective module-finite extension of
Noetherian domains descends the `N-1` condition. -/
@[stacks 032K "(1)"]
theorem of_moduleFinite
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
    (h : Function.Injective (algebraMap R S)) [IsN1Ring S] :
    IsN1Ring R := sorry

end IsN1Ring

namespace IsN2Ring

/-- Lemma 10.161.7 (2), tag `032K`: an injective module-finite extension of
Noetherian domains descends the `N-2` condition. -/
@[stacks 032K "(2)"]
theorem of_moduleFinite
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
    (h : Function.Injective (algebraMap R S)) [IsN2Ring S] :
    IsN2Ring R := sorry

end IsN2Ring

end
