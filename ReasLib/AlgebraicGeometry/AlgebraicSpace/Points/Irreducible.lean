/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sets.Closeds
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# The full irreducible closed support of an integral algebraic space

The entire point space of an integral algebraic space is an irreducible closed
subset in its canonical topology.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The full point space of an integral algebraic space as an irreducible closed subset. -/
def univIrreducibleClosed {S : Scheme.{u}} (X : AlgebraicSpace S) [IsIntegral X] :
    IrreducibleCloseds (Points X) where
  carrier := Set.univ
  isIrreducible' :=
    (irreducibleSpace_def (Points X)).mp
      (IsIrreducible.spec X (fun U p hp hsurj ↦
        (Points.isOpenQuotientMap_mapOfOver (U := U) p hp hsurj).isQuotientMap))
  isClosed' := isClosed_univ

/-- The full irreducible closed support has carrier equal to the entire point space. -/
theorem coe_univIrreducibleClosed {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsIntegral X] :
    (univIrreducibleClosed X : Set (Points X)) = Set.univ :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
