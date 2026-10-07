module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_16_1_ChangeOfBase
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap78.Definition_78_5_1_Group

/-!
# Group algebraic spaces over fields after algebraic closure

A separated group algebraic space over a field becomes a scheme after base
change to the algebraic closure.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- Lemma 79.10.1: Let `k` be a field with algebraic closure `AlgebraicClosure k`.
Let `G` be a group algebraic space over `k` which is separated. Then
`G_{AlgebraicClosure k}`, formed as
`baseChange (FieldExtension.specMap k (AlgebraicClosure k)) G.X.left`, is a
scheme. -/
@[stacks 0B8E]
theorem isScheme_baseChange_algebraicClosure {k : Type u} [Field k]
    (G : GroupAlgebraicSpace (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
    [AlgebraicSpace.IsSeparated G.X.left] :
    AlgebraicSpace.IsScheme
      (baseChange (FieldExtension.specMap k (AlgebraicClosure k)) G.X.left) := sorry

end AlgebraicGeometry.GroupAlgebraicSpace
