/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import ReasLib.RingTheory.AdicCompletion.TopologicallyFiniteType

/-!
# Topologically finite type over an extended ideal

Topological finite type passes to an intermediate base in a compatible algebra tower.
-/

@[expose] public section

universe u

namespace Algebra.TopologicallyFiniteType

variable {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]

/-- `I`-adic completeness of a topologically finite type algebra is equivalent
to completeness along the extended ideal `I C`. -/
instance instMapAlgebraMap (I : Ideal A) [TopologicallyFiniteType I C] :
    IsAdicComplete (I.map (algebraMap A C)) C :=
  (IsAdicComplete.map_algebraMap_iff (R := A) (S := C) (M := C) I).mpr inferInstance

variable {B : Type u} [CommRing B] [Algebra A B] [Algebra B C] [IsScalarTower A B C]

/-- In a compatible tower of topologically finite type algebras, the top algebra
is topologically of finite type over the intermediate algebra along the extended ideal. -/
instance instMapIdeal (I : Ideal A)
    [TopologicallyFiniteType I B] [TopologicallyFiniteType I C] :
    TopologicallyFiniteType (I.map (algebraMap A B)) C := sorry

end Algebra.TopologicallyFiniteType
