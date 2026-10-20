/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Defs.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocal
public import ReasLib.AlgebraicGeometry.Scheme.Reduced.Etale

/-!
# Reduced closed subspaces of algebraic spaces

A closed subset `T ⊂ |X|` of the points of an algebraic space is the underlying
point-set of a unique reduced closed subspace `Z ⊂ X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubspace

/-- The underlying set of points of a closed subspace, as the image of `|Z| → |X|`. -/
def pointsSet {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X) :
    Set (Points X) :=
  Set.range (Points.map Z.ι)

/-- `pointsSet Z` is the range of `Points.map Z.ι`. -/
theorem pointsSet_eq {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X) :
    Z.pointsSet = Set.range (Points.map Z.ι) :=
  sorry

/-- A point of `|X|` lies in `pointsSet Z` if and only if it is the image of a point of `|Z|`. -/
theorem mem_pointsSet {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X)
    {x : Points X} :
    x ∈ Z.pointsSet ↔ ∃ y : Points Z.X, Points.map Z.ι y = x :=
  sorry

/-- The image `|Z| ⊆ |X|` is closed in the canonical topology on `|X|`. -/
theorem isClosed_pointsSet {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X) :
    IsClosed (Z.pointsSet : Set (Points X)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ClosedSubspace
