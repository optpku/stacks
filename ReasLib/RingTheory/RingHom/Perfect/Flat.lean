/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.FinitePresentation
public import ReasLib.RingTheory.RingHom.Perfect.Presentation

/-!
# Flat finitely presented ring maps

Flat finite-presentation maps form a canonical source of perfect ring maps.

@stack 067J
-/

@[expose] public section

universe u v

namespace Algebra

/-- A flat finitely presented commutative algebra map is perfect. -/
@[stacks 067J "flat finitely presented map"]
instance instIsPerfectRingMapOfFlatOfFinitePresentation
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.FinitePresentation A B] :
    (algebraMap A B).IsPerfectRingMap := sorry
/- Proof strategy: apply the polynomial-presentation criterion. Finite presentation gives a
finite presentation of the restricted target module, while flatness gives Tor amplitude in degree
zero; the pseudo-coherent plus finite-Tor criterion then makes that module perfect. -/

end Algebra
