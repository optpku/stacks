module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group.Representability

/-!
# Group algebraic spaces of finite type over a field

A separated group algebraic space locally of finite type over a field is a
scheme.
-/

@[expose] public section

universe u

open CategoryTheory

/- Lemma 79.10.2: Let `k` be a field. Let `G` be a group algebraic space over
`k`. If `G` is separated and locally of finite type over `k`, then `G` is a
scheme. -/
@[stacks 0B8F] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.isScheme_of_isSeparated_locallyOfFiniteType :
    ∀ {k : Type u} [Field k]
      (G : AlgebraicGeometry.GroupAlgebraicSpace
        (AlgebraicGeometry.AlgebraicSpace.ofOver
          (CategoryTheory.Over.mk (𝟙 (AlgebraicGeometry.Spec (CommRingCat.of k))))))
      [AlgebraicGeometry.AlgebraicSpace.IsSeparated G.X.left]
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType
        (AlgebraicGeometry.AlgebraicSpace.SchemeRealization.toBase G.X.left)],
      AlgebraicGeometry.AlgebraicSpace.IsScheme G.X.left)
