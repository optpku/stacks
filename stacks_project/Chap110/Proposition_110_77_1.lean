module

public import ReasLib.Algebra.Category.ModuleCat.Localization.Torsion
public import ReasLib.Algebra.Category.ModuleCat.Localization.SerreQuotient
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

namespace ModuleCat

variable {R : Type u} [CommRing R] [Small.{v} R] (S : Submonoid R)

/- Proposition 110.77.1: the Serre quotient of `ModuleCat A` by the `S`-torsion modules is
canonically equivalent to `ModuleCat (Localization S)`, via the induced functor of
localization `M ↦ S⁻¹M ≅ M ⊗[A] Localization S`. -/
@[stacks 0EA5]
#check (ModuleCat.inducedLocalizedFunctor_isEquivalence S :
  (ModuleCat.inducedLocalizedFunctor S).IsEquivalence)

end ModuleCat
