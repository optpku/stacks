/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group.Representability

/-!
# Separated group algebraic spaces over a field

A separated group algebraic space over a field is a scheme.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

/- Proposition 79.10.3: Let `k` be a field. Let `G` be a group algebraic space
over `k`. If `G` is separated, then `G` is a scheme. -/
@[stacks 0B8G] #check
  (AlgebraicGeometry.GroupAlgebraicSpace.isScheme_of_isSeparated :
    ∀ {k : Type u} [Field k]
    (G : GroupAlgebraicSpace (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
    [AlgebraicSpace.IsSeparated G.X.left],
    AlgebraicSpace.IsScheme G.X.left)
