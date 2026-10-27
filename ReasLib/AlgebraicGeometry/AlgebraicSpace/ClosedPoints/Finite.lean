/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sets.Closeds
public import ReasLib.Topology.ClosedPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Complement

/-! # Complements of finite families of closed points of algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

variable {ι : Type v} [Finite ι] {S : Scheme.{u}}

/-- The range of a finite family of closed points as a bundled closed subset. -/
def closedPointsRange (X : AlgebraicSpace S) (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X)) : Closeds (Points X) :=
  ⟨Set.range x, TopologicalSpace.isClosed_range_closedPoints x hx⟩

/-- The open subspace complementary to a finite family of closed points. -/
abbrev closedPointsComplement (X : AlgebraicSpace S) (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X)) : AlgebraicSpace S :=
  OpenSubspace.Construction.space X (closedPointsRange X x hx).compl

/-- The inclusion of the open complement of a finite family of closed points. -/
abbrev closedPointsComplementι (X : AlgebraicSpace S) (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X)) :
    closedPointsComplement X x hx ⟶ X :=
  OpenSubspace.Construction.ι X (closedPointsRange X x hx).compl

/-- The image of the open complement is precisely the complement of the finite range. -/
theorem closedPointsComplement_spec (X : AlgebraicSpace S) (x : ι → Points X)
    (hx : ∀ i, x i ∈ closedPoints (Points X)) :
    pointsImage (closedPointsComplementι X x hx) = (Set.range x)ᶜ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
