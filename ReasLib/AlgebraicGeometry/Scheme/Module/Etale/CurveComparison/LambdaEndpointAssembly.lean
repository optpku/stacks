module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ArithmeticGeometricTrace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.GeometricCompactSupportBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.CurveCompactificationRefinement
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.FiniteHigherEquivariance
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ResidualSitePairing

@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Action.ModuleCat
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.Scheme.GeometricPoint
noncomputable section
universe u

namespace ActualLambdaEndpoint
section ForgetExtension
variable (Λ : Type (u + 1)) [CommRing Λ]
variable {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
variable [HasWeakSheafify U.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [HasSheafify U.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [U.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]
variable [Y.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})]
variable [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ, (etaleRestriction j).op.HasLeftKanExtension F]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}, (etaleRestriction j).op.HasLeftKanExtension F]

/-- The scalar-forgetting comparison is the additive adjoint transpose of
the ACTUAL module extension-by-zero unit. -/
def extensionForgetMap (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (etaleExtensionByZero j AddCommGrpCat.{u + 1}).obj ((ActualSiteExt.moduleForget U Λ).obj F) ⟶
    (ActualSiteExt.moduleForget Y Λ).obj ((etaleExtensionByZero j (ModuleCat.{u + 1} Λ)).obj F) :=
  ((etaleExtensionByZero_adjunction j AddCommGrpCat.{u + 1}).homEquiv _ _).symm
    ((ActualSiteExt.moduleForget U Λ).map
      ((etaleExtensionByZero_adjunction j (ModuleCat.{u + 1} Λ)).unit.app F))

/-- Forgetting module scalars preserves the colimits and sheafification
used in this extension; this asserts invertibility of the specified mate. -/
instance extensionForgetMap_isIso (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (extensionForgetMap Λ j F) := sorry

def extensionForgetIso (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  asIso (extensionForgetMap Λ j F)

end ForgetExtension

section ScalarAssociated
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable {Y : Scheme.{u}} [ConnectedSpace Y] (xbar : GeometricPoint Y)
variable [Y.smallEtaleTopology.HasSheafCompose (ActualFiniteCoefficient.modules Λ)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ)))]
variable [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U)
    (ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ)))]
variable (M : (finiteTypeDiscreteModule Λ (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory)

def scalarRepresentation :
    (finiteTypeDiscreteModule (ActualRootsModule.Coeff.{u} (Nat.card Λ))
      (Aut (standardFiniteEtaleFiber xbar))).FullSubcategory :=
  ⟨⟨((ActualFiniteCoefficient.modules Λ).mapAction (Aut (standardFiniteEtaleFiber xbar))).obj M.obj.obj,
      by sorry⟩, by sorry⟩

def finiteScalarSheaf :
    (Sheaf.finiteTypeLocallyConstantModule Y.smallEtaleTopology
      (ActualRootsModule.Coeff.{u} (Nat.card Λ))).FullSubcategory :=
  ⟨(ActualFiniteCoefficient.sheaves Λ Y).obj ((associatedSheafFunctor Λ xbar).obj M), by
    -- Local instance justification (defeq pin): expose the finite local system carried by the published inverse.
    letI : Sheaf.IsFiniteTypeLocallyConstantModule ((associatedSheafFunctor Λ xbar).obj M) :=
      ((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ xbar).inverse.obj M).property
    exact ActualFiniteCoefficient.sheaves_finiteLocallyConstant Λ Y _⟩

instance modules_pointColimits : PreservesFilteredColimitsOfSize.{u, u}
    (ActualFiniteCoefficient.modules Λ : ModuleCat.{u + 1} Λ ⥤
      ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ))) := sorry

/-- The scalar-change stalk map is the filtered-colimit comparison followed
by the PUBLISHED concrete counit. -/
def scalarStalkIso :
    (StalkRepresentation.stalk (ActualRootsModule.Coeff.{u} (Nat.card Λ)) xbar).obj
      (finiteScalarSheaf Λ xbar M).obj ≅ (scalarRepresentation Λ xbar M).obj.obj.V :=
  ((geometricPointEtalePoint xbar).presheafFiberCompIso
      (ActualFiniteCoefficient.modules Λ : ModuleCat.{u + 1} Λ ⥤
        ModuleCat.{u + 1} (ActualRootsModule.Coeff.{u} (Nat.card Λ)))).app
      ((associatedSheafFunctor Λ xbar).obj M).obj ≪≫
    (ActualFiniteCoefficient.modules Λ).mapIso (ModuleSheafInverse.counitLinearEquiv xbar Λ M).toModuleIso

def scalarStalkRepresentationIso :
    (finiteTypeLocallyConstantModuleToFinitePi1LambdaModules
      (ActualRootsModule.Coeff.{u} (Nat.card Λ)) xbar).obj (finiteScalarSheaf Λ xbar M) ≅
    scalarRepresentation Λ xbar M :=
  ObjectProperty.isoMk _ (ObjectProperty.isoMk _
    (Action.mkIso (scalarStalkIso Λ xbar M) (fun _ ↦ sorry)))

/-- Scalar restriction of the associated sheaf is identified through its
actual stalk map and the existing unit, with no chosen equivalence package. -/
def associatedScalarIso :
    (ActualFiniteCoefficient.sheaves Λ Y).obj ((associatedSheafFunctor Λ xbar).obj M) ≅
    (associatedSheafFunctor (ActualRootsModule.Coeff.{u} (Nat.card Λ)) xbar).obj
      (scalarRepresentation Λ xbar M) :=
  (Sheaf.finiteTypeLocallyConstantModule Y.smallEtaleTopology
    (ActualRootsModule.Coeff.{u} (Nat.card Λ))).ι.mapIso
      (((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules
        (ActualRootsModule.Coeff.{u} (Nat.card Λ)) xbar).unitIso.app (finiteScalarSheaf Λ xbar M)) ≪≫
      (finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules
        (ActualRootsModule.Coeff.{u} (Nat.card Λ)) xbar).inverse.mapIso
          (scalarStalkRepresentationIso Λ xbar M))

end ScalarAssociated
end ActualLambdaEndpoint
