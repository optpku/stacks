/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
public import stacks_project.Chap66.Lemma_66_13_1_SchematicLocus

/-!
# Dense schematic locus of Zariski locally quasi-separated algebraic spaces

If an algebraic space is Zariski locally quasi-separated, then its schematic
locus is a dense open subspace which is a scheme, equivalently every
codimension-zero point lies in the schematic locus.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Proposition 66.13.3 (1): Let `S` be a scheme. Let `X` be an algebraic space
over `S`. If `X` is Zariski locally quasi-separated (for example if `X` is
quasi-separated), then there exists a dense open subspace of `X` which is a
scheme. -/
@[stacks 06NH]
theorem exists_dense_open_isScheme {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAbsolutelyZariskiLocallyQuasiSeparated X] :
    ∃ X' : OpenSubspace X, IsScheme X'.X ∧ Dense X'.pointsSet :=
  sorry

/-- Proposition 66.13.3 (2): Let `S` be a scheme. Let `X` be an algebraic space
over `S`. If `X` is Zariski locally quasi-separated, then every point of
`Points X` of codimension `0` in `X` is contained in `schematicLocus X`. -/
@[stacks 06NH]
theorem codimZero_subset_schematicLocus {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAbsolutelyZariskiLocallyQuasiSeparated X] :
    (setOf fun x : Points X ↦ localRingDimAt x = 0) ⊆
      (schematicLocus X).pointsSet :=
  sorry

/-- If `X` is Zariski locally quasi-separated, then the schematic locus of `X`
is dense in `Points X`. -/
theorem dense_schematicLocus {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAbsolutelyZariskiLocallyQuasiSeparated X] :
    Dense (schematicLocus X).pointsSet :=
  sorry

/-- If `X` is Zariski locally quasi-separated, then every codimension-zero point
of `X` lies in the schematic locus. -/
theorem mem_schematicLocus_of_codimZero {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsAbsolutelyZariskiLocallyQuasiSeparated X] {x : Points X}
    (hx : localRingDimAt x = 0) :
    x ∈ (schematicLocus X).pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
