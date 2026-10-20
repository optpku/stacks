module
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.Equivalence
@[expose] public section
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace AlgebraicGeometry.Scheme
variable {X : Scheme.{u}} (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
variable [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
variable [ConnectedSpace X]
def associatedSheafFunctor (xbar : GeometricPoint X) :
    (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ xbar).inverse ⋙ (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).ι
def associatedSheaf (xbar : GeometricPoint X) (M : (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory) : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) := (associatedSheafFunctor Λ xbar).obj M
theorem associatedSheaf_obj (xbar : GeometricPoint X) (M : (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory) : associatedSheaf Λ xbar M = ((finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ xbar).inverse.obj M).obj := sorry
theorem associatedSheaf_spec (xbar : GeometricPoint X) (M : (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory) : Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ (associatedSheaf Λ xbar M) := sorry
end AlgebraicGeometry.Scheme
end
