/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.EssentialFiniteness
public import ReasLib.RingTheory.Regular.JRing
import Mathlib.Tactic.CrossRefAttribute

/-!
# Essential finite type extensions of J-2 rings

@stack 07PJ
-/

@[expose] public section

universe u v w

namespace IsJ2Ring

/-- Finite type algebras over `J-2` rings are `J-2`. -/
@[stacks 07PJ "(7), finite type extensions"]
theorem of_finiteType
    (R : Type u) {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsJ2Ring.{u, w} R] [Algebra.FiniteType R S] :
    IsJ2Ring.{v, w} S := sorry

/-- Essentially finite type algebras over `J-2` rings are `J-2`. -/
@[stacks 07PJ "essentially finite type extensions"]
theorem of_essFiniteType
    (R : Type u) {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsJ2Ring.{u, w} R] [Algebra.EssFiniteType R S] :
    IsJ2Ring.{v, w} S := sorry

end IsJ2Ring
