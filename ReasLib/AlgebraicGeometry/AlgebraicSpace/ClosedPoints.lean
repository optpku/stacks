/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.Extension

/-!
# Closed points of decent algebraic spaces

Field-valued points over closed base points have closed image when the induced
residue-field extension is algebraic.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Scheme.Hom

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A field-valued point of a decent algebraic space has closed image if its image
in the base is closed and the canonical extension from the residue field of that
base point to the source field is algebraic. -/
@[stacks 07U5]
theorem mem_closedPoints_of_isAlgebraic_residueField {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (p : FieldValuedPoint X)
    (hs : closedPointImage p.structureHom ∈ closedPoints S)
    (halg : Algebra.IsAlgebraic (S.residueField (closedPointImage p.structureHom)) p.K) :
    Points.mk p ∈ closedPoints (Points X) :=
  sorry

/-- The residue-field morphism at a closed point of a decent algebraic space is a
closed immersion. -/
@[stacks 0AHB]
theorem isClosedImmersion_fromSpecResidueField {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {x : Points X} (hx : x ∈ closedPoints (Points X)) :
    IsClosedImmersion (X.fromSpecResidueField x) :=
  sorry

/-- A closed point of a decent algebraic space is represented by a closed immersion
from the spectrum of a field. -/
theorem exists_fieldValuedPoint_isClosedImmersion {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {x : Points X} (hx : x ∈ closedPoints (Points X)) :
    ∃ p : FieldValuedPoint X, IsClosedImmersion p.hom ∧ Points.mk p = x :=
  ⟨FieldValuedPoint.residuePoint x, isClosedImmersion_fromSpecResidueField hx,
    FieldValuedPoint.mk_residuePoint x⟩

/-- The residue-field morphism of a decent algebraic space is a closed immersion
when its point is closed. -/
instance fromSpecResidueField.isClosedImmersion {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] (x : Points X) [Fact (x ∈ closedPoints (Points X))] :
    IsClosedImmersion (X.fromSpecResidueField x) :=
  isClosedImmersion_fromSpecResidueField Fact.out

end AlgebraicGeometry.AlgebraicSpace
