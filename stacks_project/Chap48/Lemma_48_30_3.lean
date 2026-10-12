/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.ProExtension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.ModuleDerived
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe v

/- Lemma 48.30.3 (1): every morphism between the constant restricted values of two Deligne
systems extends uniquely to a morphism between their pro-objects. -/
@[stacks 0G4L] #check
  (@AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.existsUnique_proHom_restrictsTo :
    ∀ {X U : Scheme.{v}} {j : U ⟶ X} [IsNoetherian X] [IsNoetherian U]
      [IsOpenImmersion j] (S T : DeligneSystem j)
      (α : (ambient (SheafOfModules.isCoherent U.ringCatSheaf)).obj S.value ⟶
        (ambient (SheafOfModules.isCoherent U.ringCatSheaf)).obj T.value),
      ∃! f : S.proObject ⟶ T.proObject, DeligneSystem.RestrictsTo S T f α)

/- Lemma 48.30.3 (2): every bounded complex with coherent cohomology on `U` is the constant
restricted value of a Deligne system on `X`. -/
@[stacks 0G4L] #check
  (@AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.exists_deligneSystem_withValue :
    ∀ {X U : Scheme.{v}} {j : U ⟶ X} [IsNoetherian X] [IsNoetherian U]
      [IsOpenImmersion j] (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]),
      ∃ S : DeligneSystem j, S.value = K)

/- Lemma 48.30.3 (3): two Deligne systems extending the same bounded coherent object determine
uniquely isomorphic pro-objects, with the isomorphism restricting to the chosen identification of
their values. -/
@[stacks 0G4L] #check
  (@AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.existsUnique_proIso_restrictsTo :
    ∀ {X U : Scheme.{v}} {j : U ⟶ X} [IsNoetherian X] [IsNoetherian U]
      [IsOpenImmersion j] (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
      (S T : DeligneSystem j) (eS : S.value ≅ K) (eT : T.value ≅ K),
      ∃! e : S.proObject ≅ T.proObject,
        DeligneSystem.RestrictsTo S T e.hom
          ((ambient (SheafOfModules.isCoherent U.ringCatSheaf)).map (eS.hom ≫ eT.inv)))
