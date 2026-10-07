module

public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap100.Lemma_100_11_2_Reduced
public import stacks_project.Chap100.Lemma_100_11_3_LocallyNoetherian
public import stacks_project.Chap100.Lemma_100_11_10_Regular

/-!
# Regularity of reduced locally Noetherian singleton algebraic stacks

A reduced, locally Noetherian algebraic stack whose space of points is a
singleton is regular.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 100.11.10: A reduced, locally Noetherian algebraic stack `Z` such that
`|Z|` is a singleton is regular. -/
@[stacks 06MV]
instance isRegular_of_isReduced_isLocallyNoetherian_subsingleton
    {S : Scheme.{u}} (Z : GroupoidsOver S) [AlgebraicStack Z] [IsReduced Z]
    [IsLocallyNoetherian Z] [Nonempty (Points Z)] [Subsingleton (Points Z)] :
    IsRegular Z :=
  sorry

end AlgebraicGeometry.AlgebraicStack
