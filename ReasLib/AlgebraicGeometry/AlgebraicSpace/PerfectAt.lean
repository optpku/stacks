/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion

/-!
# Pointwise perfectness of morphisms of algebraic spaces

A morphism of algebraic spaces is perfect at a point when its restriction to
some open subspace neighbourhood is perfect.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is perfect at a point if its restriction to
some open subspace neighbourhood of that point is perfect. -/
def PerfectAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
    IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ Perfect (i ≫ f)

/-- Perfectness at a point is equivalent to the existence of an open subspace
neighbourhood on which the morphism is perfect. -/
theorem perfectAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) :
    PerfectAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ Perfect (i ≫ f) :=
  Iff.rfl

end AlgebraicGeometry.AlgebraicSpace
