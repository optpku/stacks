/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.RationalMap.FiniteComponents

/- Remark 29.49.13: schemes whose quasi-compact opens have finitely many
irreducible components form a category with generic-point-preserving rational
maps as morphisms. -/
@[stacks 0BX9] #check (AlgebraicGeometry.FiniteComponentRationalMapCat.instCategory :
    CategoryTheory.Category AlgebraicGeometry.FiniteComponentRationalMapCat)
