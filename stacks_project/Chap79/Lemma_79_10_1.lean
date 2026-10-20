/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group.Representability

/-!
# Group algebraic spaces over fields after algebraic closure

A separated group algebraic space over a field becomes a scheme after base
change to the algebraic closure.
-/

@[expose] public section

universe u

open CategoryTheory

/- Lemma 79.10.1: Let `k` be a field with algebraic closure `AlgebraicClosure k`.
Let `G` be a group algebraic space over `k` which is separated. Then
`G_{AlgebraicClosure k}`, formed as
`baseChange (FieldExtension.specMap k (AlgebraicClosure k)) G.X.left`, is a
scheme. -/
@[stacks 0B8E] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.isScheme_baseChange_algebraicClosure :
    ∀ {k : Type u} [Field k]
      (G : AlgebraicGeometry.GroupAlgebraicSpace
        (AlgebraicGeometry.AlgebraicSpace.ofOver
          (CategoryTheory.Over.mk (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of k))))))
      [AlgebraicGeometry.AlgebraicSpace.IsSeparated G.X.left],
      AlgebraicGeometry.AlgebraicSpace.IsScheme
        (AlgebraicGeometry.AlgebraicSpace.baseChange
          (AlgebraicGeometry.FieldExtension.specMap k (AlgebraicClosure k)) G.X.left))
