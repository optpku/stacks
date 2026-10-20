/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.SchematicLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reasonable

/-!
# Dense schematic locus of reasonable algebraic spaces

The schematic locus of a reasonable algebraic space is dense, giving a dense open
subspace that is representable by a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The schematic locus of a reasonable algebraic space is dense in its space of points. -/
theorem dense_schematicLocus_of_isReasonable {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsReasonable X] :
    Dense (schematicLocus X).pointsSet :=
  sorry

/-- Every reasonable algebraic space has a dense open subspace representable by a scheme. -/
theorem exists_dense_open_isScheme_of_isReasonable {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsReasonable X] :
    ∃ X' : OpenSubspace X, IsScheme X'.X ∧ Dense X'.pointsSet :=
  ⟨schematicLocus X, instIsScheme_schematicLocus X, dense_schematicLocus_of_isReasonable X⟩

end AlgebraicGeometry.AlgebraicSpace
