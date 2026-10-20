module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LocalizationAway

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open ComplexShape

noncomputable section

universe u v w z

namespace RingedSite.Hom.ModuleDerived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}} [UnivLE.{max u v, z}]

#check (RingedSite.Hom.ModuleDerived.localSectionActionComplex_comm :
    ∀ (K : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O))
    (U : C) (f : O.obj.obj (op U)) (i j : ℤ) (hij : (up ℤ).Rel i j),
    SheafOfModules.sectionActionHom O
        ((DerivedCategory.Q.objPreimage K).X i) U f ≫
      ((localizedRestrictionComplex.{z}
        (RingedSite.ofCommRingSheaf J O) U).obj
          (DerivedCategory.Q.objPreimage K)).d i j =
    ((localizedRestrictionComplex.{z}
        (RingedSite.ofCommRingSheaf J O) U).obj
          (DerivedCategory.Q.objPreimage K)).d i j ≫
      SheafOfModules.sectionActionHom O
        ((DerivedCategory.Q.objPreimage K).X j) U f)

#check (RingedSite.Hom.ModuleDerived.localSectionActionComplex :
    ∀ (K : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O))
    (U : C) (f : O.obj.obj (op U)),
    End ((localizedRestrictionComplex.{z}
      (RingedSite.ofCommRingSheaf J O) U).obj
        (DerivedCategory.Q.objPreimage K)))

#check (RingedSite.Hom.ModuleDerived.localSectionActionComplex_f :
    ∀ (K : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O))
    (U : C) (f : O.obj.obj (op U)) (i : ℤ),
    (localSectionActionComplex K U f).f i =
      SheafOfModules.sectionActionHom O
        ((DerivedCategory.Q.objPreimage K).X i) U f)

#check (RingedSite.Hom.ModuleDerived.localSectionAction_naturality :
    ∀ (U : C) (f : O.obj.obj (op U))
    {M N : ModuleCat.{z} (RingedSite.ofCommRingSheaf J O)} (g : M ⟶ N),
    (localizedRestriction.{z} (RingedSite.ofCommRingSheaf J O) U).map g ≫
        SheafOfModules.sectionActionHom O N U f =
      SheafOfModules.sectionActionHom O M U f ≫
        (localizedRestriction.{z} (RingedSite.ofCommRingSheaf J O) U).map g)

#check (RingedSite.Hom.ModuleDerived.localSectionActionNatTrans :
    ∀ (U : C) (f : O.obj.obj (op U)),
    localizedRestriction.{z} (RingedSite.ofCommRingSheaf J O) U ⟶
      localizedRestriction.{z} (RingedSite.ofCommRingSheaf J O) U)

#check (RingedSite.Hom.ModuleDerived.localSectionActionNatTrans_app :
    ∀ (U : C) (f : O.obj.obj (op U))
    (M : ModuleCat.{z} (RingedSite.ofCommRingSheaf J O)),
    (localSectionActionNatTrans U f).app M =
      SheafOfModules.sectionActionHom O M U f)

#check (RingedSite.Hom.ModuleDerived.localizedRestrictionExact :
    ∀ (U : C),
    ExactFunctor (ModuleCat.{z} (RingedSite.ofCommRingSheaf J O))
      (ModuleCat.{z} ((RingedSite.ofCommRingSheaf J O).localization U)))

#check (RingedSite.Hom.ModuleDerived.localizedRestrictionExact_obj :
    ∀ (U : C),
    (localizedRestrictionExact (O := O) U).obj =
      localizedRestriction.{z} (RingedSite.ofCommRingSheaf J O) U)

#check (RingedSite.Hom.ModuleDerived.localSectionActionExact :
    ∀ (U : C) (f : O.obj.obj (op U)),
    localizedRestrictionExact (O := O) U ⟶ localizedRestrictionExact (O := O) U)

#check (RingedSite.Hom.ModuleDerived.localSectionActionExact_hom :
    ∀ (U : C) (f : O.obj.obj (op U)),
    (localSectionActionExact (O := O) U f).hom = localSectionActionNatTrans U f)

#check (RingedSite.Hom.ModuleDerived.localSectionAction :
    ∀ (K : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O))
    (U : C) (f : O.obj.obj (op U)),
    End ((localizedRestrictionDerived.{z}
      (RingedSite.ofCommRingSheaf J O) U).obj K))

#check (RingedSite.Hom.ModuleDerived.localSectionAction_eq :
    ∀ (K : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O))
    (U : C) (f : O.obj.obj (op U)),
    localSectionAction K U f =
      (@ExactFunctor.MapDerivedCategory.map
        _ _ _ (RingedSite.Hom.moduleCat_hasDerivedCategory
          (RingedSite.ofCommRingSheaf J O))
        _ _ _ (RingedSite.Hom.localizedModuleCatHasDerivedCategory
          (X := RingedSite.ofCommRingSheaf J O) U)
        _ _ (localSectionActionExact (O := O) U f)).app K)

#check (RingedSite.Hom.ModuleDerived.localizationAwayTower :
    ∀ (K : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O))
    (U : C) (f : O.obj.obj (op U)),
    SequentialInverseSystem
      (ModuleDerived.{z} ((RingedSite.ofCommRingSheaf J O).localization U)))

#check (RingedSite.Hom.ModuleDerived.localizationAwayTower_obj :
    ∀ (K : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O))
    (U : C) (f : O.obj.obj (op U)) (n : ℕᵒᵖ),
    (localizationAwayTower K U f).obj n =
      (localizedRestrictionDerived.{z}
        (RingedSite.ofCommRingSheaf J O) U).obj K)

#check (RingedSite.Hom.ModuleDerived.localizationAwayTower_map_succ :
    ∀ (K : ModuleDerived.{z} (RingedSite.ofCommRingSheaf J O))
    (U : C) (f : O.obj.obj (op U)) (n : ℕ),
    (localizationAwayTower K U f).map
      (homOfLE (Nat.le_add_right n 1)).op = localSectionAction K U f)

end RingedSite.Hom.ModuleDerived
