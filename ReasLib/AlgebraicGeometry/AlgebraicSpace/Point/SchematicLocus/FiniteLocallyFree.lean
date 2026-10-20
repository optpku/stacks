/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.SchematicLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Schematic locus along a surjective finite locally free morphism

A point of the target of a surjective finite locally free morphism of algebraic
spaces lies in the schematic locus if and only if some affine open of the source
contains the set-theoretic fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A point of the target of a surjective finite locally free morphism of
algebraic spaces lies in the schematic locus if and only if an affine open
subspace of the source contains its entire fibre. -/
theorem mem_schematicLocus_iff_exists_affineOpen {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Surjective f] [FiniteLocallyFree f]
    (y : Points Y) :
    y ∈ (schematicLocus Y).pointsSet ↔
      ∃ U : OpenSubspace X, IsAffine U.X ∧ Points.map f ⁻¹' {y} ⊆ U.pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
