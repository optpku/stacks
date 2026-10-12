/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_10_3_LocalRingDim
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap66.Lemma_66_13_1_SchematicLocus

/-!
# Open scheme neighbourhoods of points of local dimension at most one

On a separated locally Noetherian algebraic space, every point of local-ring
dimension at most one lies in an open subspace which is a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 72.9.3: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `x` be a point of `X`. If `X` is separated and locally Noetherian, and the
dimension of the local ring of `X` at `x` is at most `1`, then there exists an
open subspace of `X` containing `x` which is a scheme. -/
@[stacks 0ADD]
theorem exists_open_isScheme_of_localRingDimAt_le_one {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsAbsolutelySeparated X] [IsLocallyNoetherian X]
    (x : Points X) (hx : localRingDimAt x ≤ 1) :
    ∃ U : OpenSubspace X, IsScheme U.X ∧ x ∈ U.pointsSet :=
  sorry

/-- On a separated locally Noetherian algebraic space, every point of local-ring
dimension at most one lies in the schematic locus. -/
theorem mem_schematicLocus_of_localRingDimAt_le_one {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsAbsolutelySeparated X] [IsLocallyNoetherian X]
    {x : Points X} (hx : localRingDimAt x ≤ 1) :
    x ∈ (schematicLocus X).pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
