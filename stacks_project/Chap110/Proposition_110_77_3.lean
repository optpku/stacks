module

public import stacks_project.Chap110.Proposition_110_77_3_Equivalence
public import stacks_project.Chap110.Proposition_110_77_3_Torsion

@[expose] public section

open CategoryTheory

universe v u

namespace FGModuleCat

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Small.{v} R]

/-- Proposition 110.77.3: for a Noetherian integral domain `R` with fraction field
`FractionRing R`, the Serre quotient of `FGModuleCat R` by the Serre class of
finitely generated torsion modules is canonically equivalent to
`FGModuleCat (FractionRing R)`, the category of finite-dimensional
`FractionRing R`-vector spaces. -/
@[stacks 0B0L]
theorem inducedLocalizedFunctor_isEquivalence :
    (inducedLocalizedFunctor :
      isTorsion.isoModSerre.Localization ⥤
        FGModuleCat.{v} (FractionRing R)).IsEquivalence :=
  sorry

end FGModuleCat
