module

public import stacks_project.Chap63.Lemma_63_9_2_Comparison
public import stacks_project.Chap63.Lemma_63_9_3_Compactification

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Compactification

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace etaleDerivedLowerShriek

-- Local instance justification (search instability): prioritize the existing strong-to-weak projection so base-topology goals do not repeatedly match unrelated over-site families.
attribute [local instance 10000] HasSheafify.isRightAdjoint

variable {Y Z T : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z) (h : Z ⟶ T)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [IsSeparated h] [Scheme.Hom.FiniteType h]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  [CompactSpace T] [QuasiSeparatedSpace T]
  (A : AssocDiagram X g h)

  [IsOpenImmersion (CompDiagram.ιBase X g A.compFG)]
  [Etale (CompDiagram.ιBase X g A.compFG)]
  [IsSeparated (CompDiagram.ιBase X g A.compFG)]
  [LocallyQuasiFinite (CompDiagram.ιBase X g A.compFG)]
  [LocallyOfFiniteType (CompDiagram.ιBase X g A.compFG)]
  [IsSeparated (CompDiagram.openImmersion X g A.compFG)]
  [LocallyQuasiFinite (CompDiagram.openImmersion X g A.compFG)]
  [LocallyOfFiniteType (CompDiagram.openImmersion X g A.compFG)]
  [IsSeparated (CompDiagram.ιInterior X g A.compFG)]
  [LocallyQuasiFinite (CompDiagram.ιInterior X g A.compFG)]
  [LocallyOfFiniteType (CompDiagram.ιInterior X g A.compFG)]
  [IsSeparated (CompDiagram.ιInterior X g A.compFG ≫ CompDiagram.openImmersion X g A.compFG)]
  [LocallyQuasiFinite
  (CompDiagram.ιInterior X g A.compFG ≫ CompDiagram.openImmersion X g A.compFG)]
  [LocallyOfFiniteType
  (CompDiagram.ιInterior X g A.compFG ≫ CompDiagram.openImmersion X g A.compFG)]

  (Λ : Type u) [CommRing Λ]
  [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Z.Etale,
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify (CompDiagram.interior X g A.compFG).smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : (CompDiagram.interior X g A.compFG).Etale,
  HasWeakSheafify ((CompDiagram.interior X g A.compFG).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf (CompDiagram.interior X g A.compFG).smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify A.compFG.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : A.compFG.P_bar.obj.right.left.Etale,
  HasWeakSheafify (A.compFG.P_bar.obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf A.compFG.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify A.compFG.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : A.compFG.P_g.obj.right.left.Etale,
  HasWeakSheafify (A.compFG.P_g.obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf A.compFG.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]

  [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify (CompDiagram.interior X g A.compFG).smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify A.compFG.P_bar.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify A.compFG.P_g.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafCompose X.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose Y.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose (CompDiagram.interior X g A.compFG).smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose A.compFG.P_bar.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose A.compFG.P_g.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(CompDiagram.interior X g A.compFG).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [A.compFG.P_bar.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [A.compFG.P_g.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

  [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (CompDiagram.ιInterior X g A.compFG)).op.HasLeftKanExtension F]
  [∀ F : (CompDiagram.interior X g A.compFG).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (CompDiagram.openImmersion X g A.compFG)).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction
    (CompDiagram.ιInterior X g A.compFG ≫ CompDiagram.openImmersion X g A.compFG)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (CompDiagram.ιBase X g A.compFG)).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (CompDiagram.ιInterior X g A.compFG)).op.HasLeftKanExtension F]
  [∀ F : (CompDiagram.interior X g A.compFG).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (CompDiagram.openImmersion X g A.compFG)).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction
    (CompDiagram.ιInterior X g A.compFG ≫ CompDiagram.openImmersion X g A.compFG)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (CompDiagram.ιBase X g A.compFG)).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (CompDiagram.ιInterior X g A.compFG)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (CompDiagram.openImmersion X g A.compFG)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction
    (CompDiagram.ιInterior X g A.compFG ≫ CompDiagram.openImmersion X g A.compFG)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (CompDiagram.ιBase X g A.compFG)).op]

  [(etaleExtensionByZero (CompDiagram.ιInterior X g A.compFG)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero (CompDiagram.ιInterior X g A.compFG) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero (CompDiagram.ιInterior X g A.compFG) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (CompDiagram.ιBase X g A.compFG) (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits (etaleExtensionByZero (CompDiagram.ιBase X g A.compFG) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits (etaleExtensionByZero (CompDiagram.ιBase X g A.compFG) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (CompDiagram.openImmersion X g A.compFG)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero (CompDiagram.openImmersion X g A.compFG) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero (CompDiagram.openImmersion X g A.compFG) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero
    (CompDiagram.ιInterior X g A.compFG ≫ CompDiagram.openImmersion X g A.compFG)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits (etaleExtensionByZero
    (CompDiagram.ιInterior X g A.compFG ≫ CompDiagram.openImmersion X g A.compFG)
    (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits (etaleExtensionByZero
    (CompDiagram.ιInterior X g A.compFG ≫ CompDiagram.openImmersion X g A.compFG)
    (ModuleCat.{u} Λ))]

  [((smallEtalePullback (CompDiagram.toBase X g A.compFG)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    (CompDiagram.interior X g A.compFG).smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (CompDiagram.toBase X g A.compFG)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      (CompDiagram.interior X g A.compFG).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.interior X g A.compFG).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [((smallEtalePullback A.compFG.P_bar.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) A.compFG.P_g.obj.right.left.smallEtaleTopology
    A.compFG.P_bar.obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback A.compFG.P_bar.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) A.compFG.P_g.obj.right.left.smallEtaleTopology
      A.compFG.P_bar.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf A.compFG.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [((smallEtalePullback A.compFG.P_g.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Z.smallEtaleTopology
    A.compFG.P_g.obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback A.compFG.P_g.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z.smallEtaleTopology
      A.compFG.P_g.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf A.compFG.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [((smallEtalePullback (CompDiagram.toComposite X g A.compFG)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Z.smallEtaleTopology
    A.compFG.P_bar.obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (CompDiagram.toComposite X g A.compFG)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z.smallEtaleTopology
      A.compFG.P_bar.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf A.compFG.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [(etaleModulePushforward (CompDiagram.toBase X g A.compFG) Λ).Additive]
  [(etaleModulePushforward A.compFG.P_bar.obj.right.hom Λ).Additive]
  [(etaleModulePushforward A.compFG.P_g.obj.right.hom Λ).Additive]
  [(etaleModulePushforward (CompDiagram.toComposite X g A.compFG) Λ).Additive]
  [(etaleModulePushforward A.compFG.P_bar.obj.right.hom Λ ⋙
    etaleModulePushforward A.compFG.P_g.obj.right.hom Λ).Additive]
  [(etaleModulePushforward (CompDiagram.toBase X g A.compFG) Λ ⋙
    lowerShriekModule (CompDiagram.ιBase X g A.compFG) Λ).Additive]
  [(lowerShriekModule (CompDiagram.openImmersion X g A.compFG) Λ ⋙
    etaleModulePushforward A.compFG.P_bar.obj.right.hom Λ).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleModulePushforward (CompDiagram.toBase X g A.compFG) Λ))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.interior X g A.compFG).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleModulePushforward A.compFG.P_bar.obj.right.hom Λ))
  (HomologicalComplex.quasiIso
    (Sheaf A.compFG.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleModulePushforward A.compFG.P_g.obj.right.hom Λ))
  (HomologicalComplex.quasiIso
    (Sheaf A.compFG.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleModulePushforward (CompDiagram.toComposite X g A.compFG) Λ))
  (HomologicalComplex.quasiIso
    (Sheaf A.compFG.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleModulePushforward A.compFG.P_bar.obj.right.hom Λ ⋙
      etaleModulePushforward A.compFG.P_g.obj.right.hom Λ))
  (HomologicalComplex.quasiIso
    (Sheaf A.compFG.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleModulePushforward (CompDiagram.toBase X g A.compFG) Λ ⋙
      lowerShriekModule (CompDiagram.ιBase X g A.compFG) Λ))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.interior X g A.compFG).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (lowerShriekModule (CompDiagram.openImmersion X g A.compFG) Λ ⋙
      etaleModulePushforward A.compFG.P_bar.obj.right.hom Λ))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.interior X g A.compFG).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]


/-- Probe: apply `comp` with the same instance telescope in scope. -/
def gammaA := comp X g A.compFG Λ

end etaleDerivedLowerShriek
end AlgebraicGeometry.Scheme.Etale

end

#check gammaA

