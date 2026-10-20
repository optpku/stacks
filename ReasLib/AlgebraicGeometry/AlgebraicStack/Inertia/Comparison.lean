/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Isom.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale

/-!
# Inertia comparison along a morphism of algebraic stacks

Scheme-slice morphism properties of the relative diagonal pass to the
comparison of automorphisms over an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- If the relative 2-diagonal of a morphism of algebraic stacks has a
scheme-slice morphism property, then the automorphism comparison over any
algebraic space has the same property. -/
theorem inertiaComparison_has {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {U : AlgebraicSpace S}
    (x : U.toGroupoids ⟶ X) (P : MorphismProperty (AlgebraicSpace S))
    (hP : Groupoids.Hom.has P (Hom.diagonal.{u + 1, u, u + 1} f)) :
    Groupoids.Hom.has P (isomComparison f x x) :=
  sorry

/-- If the relative 2-diagonal of `f` is étale, then so is the inertia
comparison `isomComparison f x x`. -/
theorem inertiaComparison_etale {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {U : AlgebraicSpace S}
    (x : U.toGroupoids ⟶ X)
    (hP : Groupoids.Hom.has (@AlgebraicSpace.Etale S)
      (Hom.diagonal.{u + 1, u, u + 1} f)) :
    Groupoids.Hom.has (@AlgebraicSpace.Etale S) (isomComparison f x x) :=
  inertiaComparison_has f x (@AlgebraicSpace.Etale S) hP

end AlgebraicGeometry.AlgebraicStack
