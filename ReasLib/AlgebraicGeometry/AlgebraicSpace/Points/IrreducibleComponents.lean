/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.LocallyFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Local finiteness of irreducible components

On a locally Noetherian algebraic space, the irreducible components of any
closed subset of the points space form a locally finite family.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The irreducible components of a closed subset of the point space of a
locally Noetherian algebraic space form a locally finite family. -/
theorem locallyFinite_irreducibleComponents {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsLocallyNoetherian X] {T : Set (Points X)}
    (hT : IsClosed T) :
    LocallyFinite fun W : irreducibleComponents T ↦ Subtype.val '' (W : Set T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
