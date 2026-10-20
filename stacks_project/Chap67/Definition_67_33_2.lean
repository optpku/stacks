/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 67.33.2 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
has relative dimension ≤ `d` if it has relative dimension ≤ `d` at every point of `|X|`. -/
@[stacks 06LR] #check (AlgebraicGeometry.AlgebraicSpace.RelativeDimensionLE :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → ℕ → Prop)
#check (AlgebraicGeometry.AlgebraicSpace.relativeDimensionLE_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ),
    AlgebraicGeometry.AlgebraicSpace.RelativeDimensionLE f d ↔
      ∀ x : AlgebraicGeometry.AlgebraicSpace.Points X,
        AlgebraicGeometry.AlgebraicSpace.RelativeDimensionLEAt f d x)

/- Definition 67.33.2 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
has relative dimension `d` if it has relative dimension `d` at every point of `|X|`. -/
@[stacks 06LR] #check (AlgebraicGeometry.AlgebraicSpace.RelativeDimension :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → ℕ → Prop)
#check (AlgebraicGeometry.AlgebraicSpace.relativeDimension_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ),
    AlgebraicGeometry.AlgebraicSpace.RelativeDimension f d ↔
      ∀ x : AlgebraicGeometry.AlgebraicSpace.Points X,
        AlgebraicGeometry.AlgebraicSpace.RelativeDimensionAt f d x)
