/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.SchematicLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing

/-!
# Schematic loci of Zariski locally quasi-separated algebraic spaces

The schematic locus of a Zariski locally quasi-separated algebraic space is dense
and contains every codimension-zero point.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every codimension-zero point of a Zariski locally quasi-separated algebraic
space lies in its schematic locus. -/
theorem codimZero_subset_schematicLocus {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAbsolutelyZariskiLocallyQuasiSeparated X] :
    (setOf fun x : Points X ↦ localRingDimAt x = 0) ⊆
      (schematicLocus X).pointsSet :=
  sorry

/-- The schematic locus of a Zariski locally quasi-separated algebraic space is
dense in its space of points. -/
theorem dense_schematicLocus {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAbsolutelyZariskiLocallyQuasiSeparated X] :
    Dense (schematicLocus X).pointsSet :=
  sorry

/-- A Zariski locally quasi-separated algebraic space has a dense open subspace
which is a scheme and contains every codimension-zero point. -/
theorem exists_dense_open_isScheme {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAbsolutelyZariskiLocallyQuasiSeparated X] :
    ∃ U : OpenSubspace X, IsScheme U.X ∧ Dense U.pointsSet ∧
      ∀ x : Points X, localRingDimAt x = 0 → x ∈ U.pointsSet := by
  refine ⟨schematicLocus X, (schematicLocus_spec X).2.2.2.1,
    dense_schematicLocus X, ?_⟩
  intro x hx
  exact codimZero_subset_schematicLocus X hx

/-- A codimension-zero point of a Zariski locally quasi-separated algebraic
space belongs to its schematic locus. -/
theorem mem_schematicLocus_of_codimZero {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsAbsolutelyZariskiLocallyQuasiSeparated X] {x : Points X}
    (hx : localRingDimAt x = 0) :
    x ∈ (schematicLocus X).pointsSet :=
  codimZero_subset_schematicLocus X hx

end AlgebraicGeometry.AlgebraicSpace
