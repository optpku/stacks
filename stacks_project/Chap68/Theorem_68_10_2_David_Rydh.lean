/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.SchematicLocus.Decent
import StacksCheckRecall

/-!
# Dense schematic locus of decent algebraic spaces

If an algebraic space is decent, then it has a dense open subspace which is a
scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Theorem 68.10.2 (David Rydh): Let `S` be a scheme. Let `X` be an algebraic
space over `S`. If `X` is decent, then there exists a dense open subspace of `X`
which is a scheme. -/
@[stacks 086U] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_dense_open_isScheme_of_isDecent :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X],
      ∃ X' : OpenSubspace X, IsScheme X'.X ∧ Dense X'.pointsSet)

/- If `X` is decent, then the schematic locus of `X` is dense in `Points X`. -/
#check (AlgebraicGeometry.AlgebraicSpace.dense_schematicLocus_of_isDecent :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X],
    Dense (schematicLocus X).pointsSet)

end AlgebraicGeometry.AlgebraicSpace
