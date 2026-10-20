/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.SchematicLocus.ZariskiLocallyQuasiSeparated
import StacksCheckRecall

/-!
# Dense schematic locus of Zariski locally quasi-separated algebraic spaces

If an algebraic space is Zariski locally quasi-separated, then its schematic
locus is a dense open subspace which is a scheme and contains every
codimension-zero point.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Proposition 66.13.3: A Zariski locally quasi-separated algebraic space has
a dense open subspace which is a scheme and contains every codimension-zero
point. -/
@[stacks 06NH] #check (AlgebraicGeometry.AlgebraicSpace.exists_dense_open_isScheme :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAbsolutelyZariskiLocallyQuasiSeparated X],
    ∃ U : OpenSubspace X, IsScheme U.X ∧ Dense U.pointsSet ∧
      ∀ x : Points X, localRingDimAt x = 0 → x ∈ U.pointsSet)

#check (AlgebraicGeometry.AlgebraicSpace.codimZero_subset_schematicLocus :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAbsolutelyZariskiLocallyQuasiSeparated X],
    (setOf fun x : Points X ↦ localRingDimAt x = 0) ⊆
      (schematicLocus X).pointsSet)

#check (AlgebraicGeometry.AlgebraicSpace.dense_schematicLocus :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAbsolutelyZariskiLocallyQuasiSeparated X],
    Dense (schematicLocus X).pointsSet)

#check (AlgebraicGeometry.AlgebraicSpace.mem_schematicLocus_of_codimZero :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsAbsolutelyZariskiLocallyQuasiSeparated X] {x : Points X},
    localRingDimAt x = 0 → x ∈ (schematicLocus X).pointsSet)
