/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Comparison

/-!
# Pro-extensions from Deligne systems

This module relates morphisms of the pro-objects presented by Deligne systems to morphisms
between their constant restricted values, and gives existence and uniqueness of such extensions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe v

namespace AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem

variable {X U : Scheme.{v}} {j : U ⟶ X}
variable [IsNoetherian X] [IsNoetherian U] [IsOpenImmersion j]

/-- The pro-object presented by the positive ideal-power tower of a Deligne system. -/
noncomputable abbrev proObject (S : DeligneSystem j) :
    Pro (DerivedCategory X.Modules) :=
  (@Pro.lim (DerivedCategory X.Modules) _ (OrderDual ℕ+) _ _ _ _).obj S.tower

/-- A morphism between the pro-objects of two Deligne systems restricts to `α` when its
Hom-colimit component at every target stage, transported through the two constant restriction
identifications, is `α`. -/
def RestrictsTo (S T : DeligneSystem j)
    (f : S.proObject ⟶ T.proObject)
    (α :
      (ambient (SheafOfModules.isCoherent U.ringCatSheaf)).obj S.value ⟶
        (ambient (SheafOfModules.isCoherent U.ringCatSheaf)).obj T.value) : Prop :=
  ∀ n : OrderDual ℕ+,
    S.homColimitToRestriction.app (T.tower.obj n)
        ((Pro.homColimit.homEquiv S.tower T.tower f).app (T.tower.obj n)
          ((colimit.ι (T.tower.op ⋙ coyoneda) (op n)).app
            (T.tower.obj n) (𝟙 (T.tower.obj n)))) ≫
      (Iso.hom T.restrictionIso).app n = α

/-- Restriction of a morphism of Deligne-system pro-objects is equivalent to its stagewise
Hom-colimit compatibility with the chosen constant restriction identifications. -/
theorem restrictsTo_iff (S T : DeligneSystem j)
    (f : S.proObject ⟶ T.proObject)
    (α :
      (ambient (SheafOfModules.isCoherent U.ringCatSheaf)).obj S.value ⟶
        (ambient (SheafOfModules.isCoherent U.ringCatSheaf)).obj T.value) :
    RestrictsTo S T f α ↔
      ∀ n : OrderDual ℕ+,
        S.homColimitToRestriction.app (T.tower.obj n)
            ((Pro.homColimit.homEquiv S.tower T.tower f).app (T.tower.obj n)
              ((colimit.ι (T.tower.op ⋙ coyoneda) (op n)).app
                (T.tower.obj n) (𝟙 (T.tower.obj n)))) ≫
          (Iso.hom T.restrictionIso).app n = α := sorry

/-- Every morphism between the constant restricted values of two Deligne systems extends
uniquely to a morphism between their pro-objects. -/
theorem existsUnique_proHom_restrictsTo (S T : DeligneSystem j)
    (α :
      (ambient (SheafOfModules.isCoherent U.ringCatSheaf)).obj S.value ⟶
        (ambient (SheafOfModules.isCoherent U.ringCatSheaf)).obj T.value) :
    ∃! f : S.proObject ⟶ T.proObject,
      RestrictsTo S T f α := sorry

/-- Every bounded complex with coherent cohomology on the open subscheme is the constant
restricted value of a Deligne system. -/
theorem exists_deligneSystem_withValue
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf]) :
    ∃ S : DeligneSystem j, S.value = K := sorry

/-- Two Deligne systems extending the same bounded coherent object determine uniquely
isomorphic pro-objects, compatibly with the chosen identifications of their values. -/
theorem existsUnique_proIso_restrictsTo
    (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])
    (S T : DeligneSystem j) (eS : S.value ≅ K) (eT : T.value ≅ K) :
    ∃! e : S.proObject ≅ T.proObject,
      RestrictsTo S T e.hom
        ((ambient (SheafOfModules.isCoherent U.ringCatSheaf)).map (eS.hom ≫ eT.inv)) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem
