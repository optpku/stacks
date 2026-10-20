/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.Immersion
import StacksCheckRecall

universe u

/- Lemma 39.7.8: Let `i : G' ⟶ G` be an immersion of group schemes over a field `k`.
Then `i` is a closed immersion. -/
@[stacks 047T] #check
  (AlgebraicGeometry.GroupScheme.isClosedImmersion_of_isImmersion :
    ∀ {k : Type u} [Field k]
      {G' G : AlgebraicGeometry.SchemeOverField k}
      [CategoryTheory.GrpObj G'] [CategoryTheory.GrpObj G]
      (i : G' ⟶ G) [CategoryTheory.IsMonHom i]
      [AlgebraicGeometry.IsImmersion i.left],
      AlgebraicGeometry.IsClosedImmersion i.left)
