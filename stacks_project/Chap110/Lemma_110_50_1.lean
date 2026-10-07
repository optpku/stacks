module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap78.Definition_78_5_1_Group

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.GroupAlgebraicSpace

/-- Lemma 110.50.1: there exists a group algebraic space of finite type over a field
which is not separated, and not even quasi-separated or locally separated. -/
@[stacks 06EA]
theorem exists_finiteType_not_separated :
    ∃ (k : Type u) (_ : Field k)
      (G : GroupAlgebraicSpace (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))),
      AlgebraicSpace.FiniteType G.X.hom ∧
        ¬ AlgebraicSpace.IsSeparated G.X.left ∧
        ¬ AlgebraicSpace.IsQuasiSeparated G.X.left ∧
        ¬ AlgebraicSpace.IsLocallySeparated G.X.left := sorry

end AlgebraicGeometry.GroupAlgebraicSpace
