/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_13_1_SchematicLocus
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_45_2_Integral

/-!
# Dense schematic locus from a finite étale scheme cover

A finite étale surjective morphism from a scheme onto an algebraic space forces
the existence of a dense open subspace which is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.10.4: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
If there exists a finite, étale, surjective morphism `U ⟶ X` where `U` is a
scheme, then there exists a dense open subspace of `X` which is a scheme. -/
@[stacks 06NG]
theorem exists_dense_open_isScheme_of_finiteEtaleCover {S : Scheme.{u}}
    {X U : AlgebraicSpace S} [IsScheme U] (f : U ⟶ X) [IsFinite f] [Etale f]
    [Surjective f] :
    ∃ X' : OpenSubspace X, IsScheme X'.X ∧ Dense X'.pointsSet :=
  sorry

/-- A finite étale surjective morphism from a scheme makes the schematic locus of
`X` dense in `Points X`. -/
theorem dense_schematicLocus_of_finiteEtaleCover {S : Scheme.{u}}
    {X U : AlgebraicSpace S} [IsScheme U] (f : U ⟶ X) [IsFinite f] [Etale f]
    [Surjective f] :
    Dense (schematicLocus X).pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
