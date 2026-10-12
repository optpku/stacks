/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_13_1_SchematicLocus
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Dense schematic locus of decent algebraic spaces

If an algebraic space is decent, then it has a dense open subspace which is a
scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Theorem 68.10.2 (David Rydh): Let `S` be a scheme. Let `X` be an algebraic
space over `S`. If `X` is decent, then there exists a dense open subspace of `X`
which is a scheme. -/
@[stacks 086U]
theorem exists_dense_open_isScheme_of_isDecent {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] :
    ∃ X' : OpenSubspace X, IsScheme X'.X ∧ Dense X'.pointsSet :=
  sorry

/-- If `X` is decent, then the schematic locus of `X` is dense in `Points X`. -/
theorem dense_schematicLocus_of_isDecent {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] :
    Dense (schematicLocus X).pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
