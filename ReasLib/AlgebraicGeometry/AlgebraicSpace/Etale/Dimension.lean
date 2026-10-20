/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale

/-!
# Dimension of algebraic spaces under étale morphisms

Étale morphisms preserve dimension at a point and local-ring dimension. Surjective étale
morphisms also preserve global dimension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale

/-- An étale morphism of algebraic spaces preserves dimension at each source point. -/
@[stacks 0A4H]
theorem dimensionAt_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (x : Points X) :
    dimensionAt x = dimensionAt (Points.map f x) :=
  sorry

/-- An étale morphism of algebraic spaces preserves the dimension of the local ring at each
source point. -/
@[stacks 0A4H]
theorem localRingDimAt_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    (x : Points X) :
    localRingDimAt x = localRingDimAt (Points.map f x) :=
  sorry

/-- A morphism of algebraic spaces that is étale and surjective on points preserves global
dimension. -/
@[stacks 0A4H]
theorem dimension_eq_of_surjective {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Etale f] (hf : Function.Surjective (Points.map f)) :
    dimension X = dimension Y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Etale
