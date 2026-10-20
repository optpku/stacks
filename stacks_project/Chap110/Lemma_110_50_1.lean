/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group.NonSeparated
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

/- Lemma 110.50.1: there exists a group algebraic space of finite type over a field
which is not separated, and not even quasi-separated or locally separated. -/
@[stacks 06EA] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.exists_finiteType_not_separated :
    ∃ (k : Type u) (_ : Field k)
      (G : GroupAlgebraicSpace
        (AlgebraicSpace.ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))),
      AlgebraicSpace.FiniteType G.X.hom ∧
        ¬ AlgebraicSpace.IsSeparated G.X.left ∧
        ¬ AlgebraicSpace.IsQuasiSeparated G.X.left ∧
        ¬ AlgebraicSpace.IsLocallySeparated G.X.left)
