/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Dimension
import StacksCheckRecall

/-!
# Dimension of algebraic spaces is invariant under étale morphisms

An étale morphism of algebraic spaces preserves dimension at a point and the dimension of
the local ring at a point. If the morphism is surjective on points, it preserves global
dimension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.22.5 (1): an étale morphism preserves dimension at each source point. -/
@[stacks 0A4H] #check (AlgebraicGeometry.AlgebraicSpace.Etale.dimensionAt_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] (x : Points X),
    dimensionAt x = dimensionAt (Points.map f x))

/- Lemma 66.22.5 (2): an étale morphism preserves local-ring dimension at each source point. -/
@[stacks 0A4H] #check (AlgebraicGeometry.AlgebraicSpace.Etale.localRingDimAt_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f] (x : Points X),
    localRingDimAt x = localRingDimAt (Points.map f x))

/- Lemma 66.22.5 (3): a surjective étale morphism preserves global dimension. -/
@[stacks 0A4H] #check (AlgebraicGeometry.AlgebraicSpace.Etale.dimension_eq_of_surjective :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (hf : Function.Surjective (Points.map f)), dimension X = dimension Y)
