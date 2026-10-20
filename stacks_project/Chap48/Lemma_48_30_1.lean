module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Comparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory DerivedCategory.Bounded.CohomologyIn
open AlgebraicGeometry.Scheme.ModuleDerived
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe v

variable {X U : Scheme.{v}} {j : U ⟶ X}
variable [IsNoetherian X] [IsNoetherian U] [IsOpenImmersion j]
variable (S : DeligneSystem j)
variable (L : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])

/- Lemma 48.30.1: for an open immersion of Noetherian schemes, restriction induces a bijection
from the colimit of morphisms out of the stages of a Deligne system to morphisms out of its
constant restricted value, for every bounded coherent target. -/
@[stacks 0G2H] #check (@AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.homColimitToRestriction_bijective :
    ∀ {X U : Scheme.{v}} {j : U ⟶ X} [IsNoetherian X] [IsNoetherian U]
      [IsOpenImmersion j]
      (S : AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem j)
      (L : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]),
      Function.Bijective
        (S.homColimitToRestriction.app
          ((ambient (SheafOfModules.isCoherent X.ringCatSheaf)).obj L)))
