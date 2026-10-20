/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

/- Semantic recall: `lean_leansearch` surfaced the exact canonical scheme-level theorem
`AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian`. Since the source statement
matches that API verbatim, this item is a direct canonical recall rather than a duplicate local
wrapper. -/

/- Lemma 28.5.7: a Noetherian scheme has a finite number of irreducible components. -/
@[stacks 0BA8]
#check (AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian :
  ∀ {X : AlgebraicGeometry.Scheme.{u}}, [AlgebraicGeometry.IsNoetherian X] →
    (irreducibleComponents X).Finite)

end AlgebraicGeometry
