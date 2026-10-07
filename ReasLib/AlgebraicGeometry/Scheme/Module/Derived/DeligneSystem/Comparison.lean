module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem
public import ReasLib.CategoryTheory.Pro.HomColimit

/-!
# The Hom-colimit comparison for a Deligne system

This module constructs the canonical map from the colimit of morphisms out of the stages of a
Deligne system to morphisms out of its constant restricted value.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe v

namespace AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem

variable {X U : Scheme.{v}} {j : U ⟶ X}
variable [IsNoetherian X] [IsNoetherian U] [IsOpenImmersion j]

/-- The functor sending an ambient derived object on `X` to morphisms from the constant value of
a Deligne system into its derived restriction to `U`. -/
noncomputable def restrictionHom (S : DeligneSystem j) :
    DerivedCategory X.Modules ⥤ Type (v + 1) :=
  RingedSpace.modulePullbackDerived j.toShHom ⋙
    coyoneda.obj (op ((DerivedCategory.Bounded.CohomologyIn.ambient
      (SheafOfModules.isCoherent U.ringCatSheaf)).obj S.value))

/-- Objectwise, `restrictionHom S` is the expected morphism type after derived restriction. -/
theorem restrictionHom_obj (S : DeligneSystem j) (L : DerivedCategory X.Modules) :
    (S.restrictionHom).obj L =
      (((DerivedCategory.Bounded.CohomologyIn.ambient
          (SheafOfModules.isCoherent U.ringCatSheaf)).obj S.value) ⟶
        (RingedSpace.modulePullbackDerived j.toShHom).obj L) := sorry

/-- The map from morphisms out of one Deligne-system stage to morphisms out of its constant
restricted value. -/
noncomputable def stageToRestriction (S : DeligneSystem j) (i : OrderDual ℕ+) :
    coyoneda.obj (op (S.tower.obj i)) ⟶ S.restrictionHom :=
  coyonedaEquiv.symm (S.restrictionIso.inv.app i)

/-- A stage morphism is sent to its derived restriction, precomposed with the chosen constant
restriction identification. -/
theorem stageToRestriction_app (S : DeligneSystem j) (i : OrderDual ℕ+)
    (L : DerivedCategory X.Modules) (f : S.tower.obj i ⟶ L) :
    (S.stageToRestriction i).app L f =
      S.restrictionIso.inv.app i ≫
        (RingedSpace.modulePullbackDerived j.toShHom).map f := sorry

/-- The stagewise restriction maps are compatible with every transition of the Deligne tower. -/
theorem stageToRestriction_naturality (S : DeligneSystem j)
    {i k : (OrderDual ℕ+)ᵒᵖ} (f : i ⟶ k) :
    ((S.tower.op ⋙ coyoneda).map f) ≫ S.stageToRestriction k.unop =
      S.stageToRestriction i.unop ≫
        ((Functor.const (OrderDual ℕ+)ᵒᵖ).obj S.restrictionHom).map f := sorry

/-- The canonical comparison from the Hom-colimit of a Deligne system to morphisms out of its
constant restricted value. -/
noncomputable def homColimitToRestriction (S : DeligneSystem j) :
    Pro.homColimit S.tower ⟶ S.restrictionHom :=
  colimit.desc (S.tower.op ⋙ coyoneda) <|
    Cocone.mk S.restrictionHom
      { app := fun i ↦ S.stageToRestriction i.unop
        naturality := fun _ _ f ↦ S.stageToRestriction_naturality f }

/-- The Hom-colimit comparison restricts on every coprojection to the corresponding stagewise
restriction map. -/
theorem homColimitToRestriction_ι (S : DeligneSystem j) (i : OrderDual ℕ+) :
    colimit.ι (S.tower.op ⋙ coyoneda) (op i) ≫ S.homColimitToRestriction =
      S.stageToRestriction i := sorry

/-- Restriction identifies the Hom-colimit of a Deligne system with morphisms from its constant
restricted value for every bounded coherent target. -/
theorem homColimitToRestriction_bijective (S : DeligneSystem j)
    (L : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    Function.Bijective
      (S.homColimitToRestriction.app
        ((DerivedCategory.Bounded.CohomologyIn.ambient
          (SheafOfModules.isCoherent X.ringCatSheaf)).obj L)) := sorry

/-- The Hom-colimit comparison is bijective for every bounded-below coherent target. -/
theorem homColimitToRestriction_bijective_of_plus (S : DeligneSystem j)
    (L : D⁺[SheafOfModules.isCoherent X.ringCatSheaf]) :
    Function.Bijective
      (S.homColimitToRestriction.app
        ((DerivedCategory.Plus.CohomologyIn.ambient
          (SheafOfModules.isCoherent X.ringCatSheaf)).obj L)) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem
