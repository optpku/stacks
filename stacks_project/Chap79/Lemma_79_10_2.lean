module

public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap78.Definition_78_5_1_Group

/-!
# Group algebraic spaces of finite type over a field

A separated group algebraic space locally of finite type over a field is a
scheme.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- Lemma 79.10.2: Let `k` be a field. Let `G` be a group algebraic space over
`k`. If `G` is separated and locally of finite type over `k`, then `G` is a
scheme. -/
@[stacks 0B8F]
theorem isScheme_of_isSeparated_locallyOfFiniteType {k : Type u} [Field k]
    (G : GroupAlgebraicSpace (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
    [AlgebraicSpace.IsSeparated G.X.left]
    [AlgebraicSpace.LocallyOfFiniteType (toBase G.X.left)] :
    AlgebraicSpace.IsScheme G.X.left := sorry

end AlgebraicGeometry.GroupAlgebraicSpace
