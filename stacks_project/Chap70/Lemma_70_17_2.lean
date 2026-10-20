/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MinimalNonscheme
import StacksCheckRecall

/-!
# Minimal nonschemes are reduced and irreducible

A quasi-compact quasi-separated algebraic space that is not a scheme, while
every proper closed subspace is a scheme, is reduced and irreducible.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 70.17.2 (1): A quasi-compact, absolutely quasi-separated minimal
nonscheme algebraic space is reduced. -/
@[stacks 0B7Z]
#check (AlgebraicGeometry.AlgebraicSpace.IsReduced.of_isMinimalNonscheme :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    [IsQuasiCompact X] → [IsAbsolutelyQuasiSeparated X] →
    IsMinimalNonscheme X → IsReduced X)

/- Lemma 70.17.2 (2): A quasi-compact, absolutely quasi-separated minimal
nonscheme algebraic space is irreducible. -/
@[stacks 0B7Z]
#check (AlgebraicGeometry.AlgebraicSpace.IsIrreducible.of_isMinimalNonscheme :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    [IsQuasiCompact X] → [IsAbsolutelyQuasiSeparated X] →
    IsMinimalNonscheme X → IsIrreducible X)

end AlgebraicGeometry.AlgebraicSpace
