module

import StacksCheckRecall
public import ReasLib.Algebra.Category.FGModuleCat.Localization

@[expose] public section

open CategoryTheory

universe v u

namespace FGModuleCat

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Small.{v} R]

/- Proposition 110.77.3: for a Noetherian integral domain `R` with fraction field
`FractionRing R`, the Serre quotient of `FGModuleCat R` by the Serre class of
finitely generated torsion modules is canonically equivalent to
`FGModuleCat (FractionRing R)`, the category of finite-dimensional
`FractionRing R`-vector spaces. -/
@[stacks 0B0L] #check (FGModuleCat.inducedLocalizedFunctor_isEquivalence :
  (FGModuleCat.inducedLocalizedFunctor :
    FGModuleCat.isTorsion.isoModSerre.Localization ⥤
      FGModuleCat.{v} (FractionRing R)).IsEquivalence)

end FGModuleCat
