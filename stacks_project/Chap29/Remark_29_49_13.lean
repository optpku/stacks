module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.RationalMap.FiniteComponents

/- Remark 29.49.13: schemes whose quasi-compact opens have finitely many
irreducible components form a category with generic-point-preserving rational
maps as morphisms. -/
@[stacks 0BX9] #check (AlgebraicGeometry.FiniteComponentRationalMapCat.instCategory :
    CategoryTheory.Category AlgebraicGeometry.FiniteComponentRationalMapCat)
