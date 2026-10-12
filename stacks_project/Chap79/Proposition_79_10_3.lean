/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap78.Definition_78_5_1_Group

/-!
# Separated group algebraic spaces over a field

A separated group algebraic space over a field is a scheme.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- Proposition 79.10.3: Let `k` be a field. Let `G` be a group algebraic space
over `k`. If `G` is separated, then `G` is a scheme. -/
@[stacks 0B8G]
theorem isScheme_of_isSeparated {k : Type u} [Field k]
    (G : GroupAlgebraicSpace (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
    [AlgebraicSpace.IsSeparated G.X.left] :
    AlgebraicSpace.IsScheme G.X.left := sorry

end AlgebraicGeometry.GroupAlgebraicSpace
