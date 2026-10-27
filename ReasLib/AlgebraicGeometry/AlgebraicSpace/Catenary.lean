/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Catenary
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Catenary algebraic spaces

Catenarity of an algebraic space is catenarity of its canonical space of points.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is catenary when its canonical space of points is catenary. -/
abbrev IsCatenary {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop :=
  TopologicalSpace.CatenarySpace (Points X)

/-- Catenarity of an algebraic space is equivalent to catenarity of its point space. -/
theorem isCatenary_iff {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsCatenary X ↔ TopologicalSpace.CatenarySpace (Points X) :=
  Iff.rfl

/-- A scheme viewed as an algebraic space is catenary precisely when its underlying
topological space is catenary. -/
theorem isCatenary_ofOver_iff {S : Scheme.{u}} (U : Over S) :
    IsCatenary (ofOver U) ↔ TopologicalSpace.CatenarySpace U.left :=
  (Homeomorph.catenarySpace_iff (ofOver.pointsHomeomorph U)).symm

/-- A catenary scheme over a base, viewed as an algebraic space, is catenary. -/
instance instIsCatenary_ofOver {S : Scheme.{u}} (U : Over S)
    [TopologicalSpace.CatenarySpace U.left] : IsCatenary (ofOver U) :=
  (isCatenary_ofOver_iff U).mpr inferInstance

end AlgebraicGeometry.AlgebraicSpace
