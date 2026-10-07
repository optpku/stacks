module

public import stacks_project.Chap110.Proposition_110_77_2_Torsion
public import stacks_project.Chap110.Proposition_110_77_1_Equivalence
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

open CategoryTheory

universe v u

namespace ModuleCat

variable {R : Type u} [CommRing R] [Small.{v} R]

/-- Proposition 110.77.2: for a commutative ring `R`, the Serre quotient of `ModuleCat R` by the
Serre class of torsion modules is canonically equivalent to `ModuleCat (FractionRing R)`, via the
induced functor of localization at the non-zero-divisors. -/
@[stacks 0B0K]
theorem inducedLocalizedFunctor_nonZeroDivisors_isEquivalence :
    (inducedLocalizedFunctor (nonZeroDivisors R) :
      isTorsion.isoModSerre.Localization ⥤ ModuleCat.{v} (FractionRing R)).IsEquivalence :=
  sorry

end ModuleCat
