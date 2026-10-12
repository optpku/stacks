/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Nagata
public import ReasLib.RingTheory.QuasiFinite.FiniteType

@[expose] public section

/-!
# Quasi-Finite Extensions of Japanese Domains

This module records permanence of the `N-2` condition under injective
quasi-finite finite-type extensions of Noetherian domains.
-/

universe u v

namespace IsN2Ring

variable {R : Type u} {S : Type v}

/-- Lemma 10.161.5, tag `032I`: an injective quasi-finite finite-type extension of a
Noetherian `N-2` domain is `N-2`. -/
@[stacks 032I]
theorem of_quasiFinite
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsDomain S] [Algebra R S]
    (hRSqf : Algebra.FiniteType.QuasiFinite R S)
    (hRS : Function.Injective (algebraMap R S)) [IsN2Ring R] :
    IsN2Ring S := sorry

end IsN2Ring
