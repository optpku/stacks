module

import StacksCheckRecall
public import ReasLib.Algebra.Category.ModuleCat.Localization.Rational

/-!
# Serre quotient of abelian groups by torsion

Identifying abelian groups with integer modules, rationalization identifies their
Serre quotient by torsion groups with the category of rational vector spaces.
-/

@[expose] public section

universe v

variable [Small.{v} ℤ]

/- Proposition 110.77.4: the quotient of the category of abelian groups modulo its
Serre subcategory of torsion groups is the category of ℚ-vector spaces.

Identifying abelian groups with `ModuleCat ℤ` via `forget₂ (ModuleCat ℤ) AddCommGrpCat`,
and torsion groups with `isTorsion` at `ℤ`, this is the equivalence of
`ModuleCat.inducedLocalizedFunctorRat` with `ModuleCat ℚ`. -/
@[stacks 0B0M] #check (ModuleCat.inducedLocalizedFunctorRat_isEquivalence :
  (ModuleCat.inducedLocalizedFunctorRat.{v}).IsEquivalence)
