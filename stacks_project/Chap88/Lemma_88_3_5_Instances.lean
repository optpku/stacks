/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.TopologicallyFiniteType.Tower

@[expose] public section

universe u

/- Topological finite type over the extended ideal in an algebra tower. -/
#check (Algebra.TopologicallyFiniteType.instMapIdeal :
  ∀ {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    {B : Type u} [CommRing B] [Algebra A B] [Algebra B C] [IsScalarTower A B C]
    (I : Ideal A) [Algebra.TopologicallyFiniteType I B] [Algebra.TopologicallyFiniteType I C],
    Algebra.TopologicallyFiniteType (I.map (algebraMap A B)) C)
