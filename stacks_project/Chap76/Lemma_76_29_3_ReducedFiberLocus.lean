/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap65.Lemma_65_16_3_Equivalence
public import stacks_project.Chap71.Lemma_71_4_1_Fiber
public import stacks_project.Chap72.Definition_72_11_1_GeometricallyReduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Fiber.GeometricallyReduced

/-!
# Geometrically reduced fibre loci of morphisms of algebraic spaces

The scheme-theoretic fibre of a morphism of algebraic spaces over a field-valued
point, viewed over that field, and the locus in `|Y|` where this fibre is
geometrically reduced. The locus is stable under arbitrary base change.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.geometricallyReducedFiberLocus :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Set (Points Y))
