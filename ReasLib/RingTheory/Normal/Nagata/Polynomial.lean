/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Nagata.Normal
public import ReasLib.RingTheory.Normal.Polynomial

@[expose] public section

/-!
# Polynomial Japanese Domains

This leaf records polynomial-ring permanence of the `N-1` and `N-2`
conditions for Noetherian domains.
-/

universe u

namespace IsN1Ring

/-- Lemma 10.161.13 (1), tag `032O`: a polynomial ring over a Noetherian
`N-1` domain is `N-1`. -/
@[stacks 032O "(1)"]
theorem polynomial {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsN1Ring R] : IsN1Ring (Polynomial R) := sorry

end IsN1Ring

namespace IsN2Ring

/-- Lemma 10.161.13 (2), tag `032O`: a polynomial ring over a Noetherian
`N-2` domain is `N-2`. -/
@[stacks 032O "(2)"]
theorem polynomial {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsN2Ring R] : IsN2Ring (Polynomial R) := sorry

end IsN2Ring
