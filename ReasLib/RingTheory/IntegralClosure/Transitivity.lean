/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Tactic.CrossRefAttribute

/-!
# Transitivity of integral closures

This leaf records the tower form of transitivity: taking the integral closure
of an integral closure gives the integral closure over the original base.

@stack 0308
-/

@[expose] public section

universe u v w x y

namespace IsIntegralClosure

variable {A : Type u} [CommRing A]
variable {B : Type v} [CommRing B] [Algebra A B]
variable {B' : Type w} [CommRing B'] [Algebra A B'] [Algebra B' B]
  [IsScalarTower A B' B]
variable {C : Type x} [CommRing C] [Algebra B' C]
variable {C' : Type y} [CommRing C'] [Algebra B' C'] [Algebra C' C]
  [IsScalarTower B' C' C]
variable [Algebra A C'] [IsScalarTower A B' C'] [Algebra A C]
  [IsScalarTower A C' C]

/-- If `B'` is the integral closure of `A` in `B` and `C'` is the integral
closure of `B'` in `C`, then `C'` is the integral closure of `A` in `C`.

This is Lemma 10.36.16 of the Stacks project. -/
@[stacks 0308]
theorem trans [IsIntegralClosure B' A B] [IsIntegralClosure C' B' C] :
    IsIntegralClosure C' A C := sorry

end IsIntegralClosure
