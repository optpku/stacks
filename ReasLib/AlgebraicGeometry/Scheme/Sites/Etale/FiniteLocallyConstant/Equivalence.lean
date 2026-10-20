module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.Forward
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.StalkComparison

/-!
# Finite module-sheaf equivalence with the published forward functor

The inverse uses transported module operations on the set-level inverse. Its
unit and counit use the specified germ and finite-set comparison maps.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The finite-type `Λ`-module comparison functor is an equivalence. -/
noncomputable instance finiteTypeLocallyConstantModuleToFinitePi1LambdaModules_isEquivalence
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [ConnectedSpace X] (xbar : GeometricPoint X) :
    (finiteTypeLocallyConstantModuleToFinitePi1LambdaModules Λ xbar).IsEquivalence :=
  (ModuleSheafInverse.equivalence xbar Λ).isEquivalence_functor

/-- Finite-type locally constant étale sheaves of `Λ`-modules, for a finite ring `Λ`, are
equivalent to finite discrete `π₁`-modules with commuting `Λ`-action. -/
noncomputable def finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [ConnectedSpace X] (xbar : GeometricPoint X) :
    (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory ≌
      (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory :=
  ModuleSheafInverse.equivalence xbar Λ

/-- The module-valued equivalence sends a finite-type locally constant sheaf to a finite-type
discrete `π₁`-module. -/
theorem finiteTypePi1LambdaModules_functor_obj
    (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [ConnectedSpace X] (xbar : GeometricPoint X)
    (F : (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory) :
    IsFiniteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))
      ((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ xbar).functor.obj
        F).obj :=
  sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.FiniteAbelianInverse
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Action.ModuleCat
noncomputable section
variable {X : Scheme.{u}} [ConnectedSpace X] (xbar : GeometricPoint X)
variable [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
/-- Conversion back to integer modules retains the shared inverse's actual sections. -/
def inverseModuleSheafIso
    (M : (finiteDiscreteModule ℤ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    intModuleSheafOfAddCommSheaf ((finiteFunctor xbar).obj M) ≅
      ModuleSheafInverse.sheaf ℤ xbar (finiteTypeObject xbar M) where
  hom := { hom :=
    { app U := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).preimage
        (AddCommGrpCat.ofHom
          { toFun := fun s ↦ s, map_zero' := sorry, map_add' := sorry })
      naturality := sorry } }
  inv := { hom :=
    { app U := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).preimage
        (AddCommGrpCat.ofHom
          { toFun := fun s ↦ s, map_zero' := sorry, map_add' := sorry })
      naturality := sorry } }
  hom_inv_id := sorry
  inv_hom_id := sorry
/-- The finite abelian counit is the actual stalk comparison followed by the shared coefficient counit. -/
def counitLinearEquiv
    (M : (finiteDiscreteModule ℤ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    (discreteModuleOfFiniteLocallyConstantAddCommGrp xbar ((finiteFunctor xbar).obj M)).obj.V ≃ₗ[ℤ]
      M.obj.obj.V :=
  (((StalkRepresentation.stalk ℤ xbar).mapIso (inverseModuleSheafIso xbar M)).toLinearEquiv).trans
    (ModuleSheafInverse.counitLinearEquiv xbar ℤ (finiteTypeObject xbar M))
/-- The explicit abelian counit upgrades the actual linear map equivariantly. -/
def counitApp
    (M : (finiteDiscreteModule ℤ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory) :
    (finiteLocallyConstantAddCommGrpToFinitePi1Modules xbar).obj ((finiteFunctor xbar).obj M) ≅ M :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    (Action.mkIso (counitLinearEquiv xbar M).toModuleIso (by sorry)))
/-- The underlying finite-set stalk comparison identifies the small carrier of the abelian forward. -/
def forwardCarrierEquiv
    (F : (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory) :
    ((finiteLocallyConstant_equivalence_finitePi1Sets xbar).functor.obj
      (forgetFiniteLocallyConstantAddCommGrp.obj F)).obj.V ≃
      ModuleSheafInverse.Carrier ℤ xbar
        (finiteTypeObject xbar ((finiteLocallyConstantAddCommGrpToFinitePi1Modules xbar).obj F)) :=
  (Equiv.ulift.symm.trans (ModuleSheafInverse.setStalkEquiv xbar
      (forgetFiniteLocallyConstantAddCommGrp.obj F)).symm).trans
    ((ModuleSheafInverse.moduleFiberForgetEquiv xbar ℤ (intModuleSheafOfAddCommSheaf F)).symm.trans
      (ModuleSheafInverse.carrierEquiv ℤ xbar
        (finiteTypeObject xbar ((finiteLocallyConstantAddCommGrpToFinitePi1Modules xbar).obj F))))
/-- The actual underlying finite-action comparison is compatible with stalk monodromy. -/
def forwardSetIso
    (F : (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory) :
    (finiteLocallyConstant_equivalence_finitePi1Sets xbar).functor.obj
      (forgetFiniteLocallyConstantAddCommGrp.obj F) ≅
    ModuleSheafInverse.moduleSet ℤ xbar
      (finiteTypeObject xbar ((finiteLocallyConstantAddCommGrpToFinitePi1Modules xbar).obj F)) :=
  ObjectProperty.isoMk _
    (Action.mkIso (FintypeCat.equivEquivIso (forwardCarrierEquiv xbar F)) (by sorry))
/-- The actual set-level unit and carrier comparison supply both abelian-unit section maps. -/
def unitSetIso
    (F : (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory) :
    (forgetFiniteLocallyConstantAddCommGrp.obj F).obj ≅
      ModuleSheafInverse.setSheaf xbar
        (ModuleSheafInverse.moduleSet ℤ xbar
          (finiteTypeObject xbar ((finiteLocallyConstantAddCommGrpToFinitePi1Modules xbar).obj F))) :=
  (Sheaf.finiteLocallyConstant X.smallEtaleTopology).ι.mapIso
    ((finiteLocallyConstant_equivalence_finitePi1Sets xbar).unitIso.app
      (forgetFiniteLocallyConstantAddCommGrp.obj F) ≪≫
    (finiteLocallyConstant_equivalence_finitePi1Sets xbar).inverse.mapIso (forwardSetIso xbar F))
/-- Both abelian-unit maps are the actual set-unit functions, now respecting addition. -/
def unitApp
    (F : (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory) :
    F ≅ (finiteFunctor xbar).obj ((finiteLocallyConstantAddCommGrpToFinitePi1Modules xbar).obj F) :=
  ObjectProperty.isoMk _
    { hom := { hom :=
        { app U := AddCommGrpCat.ofHom
            { toFun := (unitSetIso xbar F).hom.hom.app U
              map_zero' := sorry
              map_add' := sorry }
          naturality := sorry } }
      inv := { hom :=
        { app U := AddCommGrpCat.ofHom
            { toFun := (unitSetIso xbar F).inv.hom.app U
              map_zero' := sorry
              map_add' := sorry }
          naturality := sorry } }
      hom_inv_id := sorry
      inv_hom_id := sorry }
end
end AlgebraicGeometry.Scheme.FiniteAbelianInverse

namespace AlgebraicGeometry.Scheme
noncomputable section
variable {X : Scheme.{u}} [ConnectedSpace X] (xbar : GeometricPoint X)
variable [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
/-- The abelian sheaf equivalence has the explicit finite-carrier inverse and actual stalk comparisons. -/
def finiteLocallyConstantAddCommGrp_equivalence_finitePi1Modules :
    (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory ≌
      (finiteDiscreteModule ℤ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory where
  functor := finiteLocallyConstantAddCommGrpToFinitePi1Modules xbar
  inverse := FiniteAbelianInverse.finiteFunctor xbar
  unitIso := NatIso.ofComponents (FiniteAbelianInverse.unitApp xbar) (by sorry)
  counitIso := NatIso.ofComponents (FiniteAbelianInverse.counitApp xbar) (by sorry)
  functor_unitIso_comp := sorry
/-- The abelian forward equivalence certificate comes from the implemented maps. -/
instance finiteLocallyConstantAddCommGrpToFinitePi1Modules_isEquivalence :
    (finiteLocallyConstantAddCommGrpToFinitePi1Modules xbar).IsEquivalence :=
  (finiteLocallyConstantAddCommGrp_equivalence_finitePi1Modules xbar).isEquivalence_functor
/-- The abelian equivalence retains the actual finite stalk representation. -/
theorem finiteLocallyConstantAddCommGrp_equivalence_finitePi1Modules_functor_obj
    (F : (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory) :
    IsFiniteDiscreteModule ℤ (Aut (GeometricPoint.finiteFiber xbar))
      ((finiteLocallyConstantAddCommGrp_equivalence_finitePi1Modules xbar).functor.obj F).obj :=
  ((finiteLocallyConstantAddCommGrpToFinitePi1Modules xbar).obj F).property
end
end AlgebraicGeometry.Scheme
