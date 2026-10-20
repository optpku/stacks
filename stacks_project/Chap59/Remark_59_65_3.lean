module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.Pullback
public import stacks_project.Chap58.Theorem_58_6_2_InducedHom
public import stacks_project.Chap59.Lemma_59_65_1_Equivalence
public import stacks_project.Chap59.Lemma_59_65_2_Equivalence
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

/- Remark 59.65.3 (1): The monodromy equivalence for finite locally constant étale sheaves of sets commutes
with inverse image and restriction along the induced fundamental-group homomorphism. -/
@[stacks 0DV6] #check (AlgebraicGeometry.Scheme.finiteLocallyConstant_pullback_catCommSq :
    ∀ {Y X : Scheme.{u}} (f : Y ⟶ X)
    [ConnectedSpace Y] [ConnectedSpace X]
    [HasWeakSheafify Y.smallEtaleTopology (Type (u + 1))]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (Type (u + 1))]
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]
    [∀ P : X.Etaleᵒᵖ ⥤ Type (u + 1), (smallEtalePullback f).op.HasLeftKanExtension P]
    (ybar : GeometricPoint Y),
    Nonempty
      (CatCommSq (finiteLocallyConstantPullback f)
        (finiteLocallyConstant_equivalence_finitePi1Sets
          (GeometricPoint.map ybar f)).functor
        (finiteLocallyConstant_equivalence_finitePi1Sets ybar).functor
        (GeometricPoint.fundamentalGroupRestriction f ybar)))

/- Remark 59.65.3 (2): The monodromy equivalence for finite locally constant étale sheaves of abelian groups
commutes with inverse image and restriction along the induced fundamental-group homomorphism. -/
@[stacks 0DV6] #check (AlgebraicGeometry.Scheme.finiteLocallyConstantAddCommGrp_pullback_catCommSq :
    ∀ {Y X : Scheme.{u}} (f : Y ⟶ X)
    [ConnectedSpace Y] [ConnectedSpace X]
    [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (ybar : GeometricPoint Y),
    Nonempty
      (CatCommSq (finiteLocallyConstantAddCommGrpPullback f)
        (finiteLocallyConstantAddCommGrp_equivalence_finitePi1Modules
          (GeometricPoint.map ybar f)).functor
        (finiteLocallyConstantAddCommGrp_equivalence_finitePi1Modules ybar).functor
        (etaleFundamentalGroupMap_resFiniteDiscreteModule f ybar)))

/- Remark 59.65.3 (3): The monodromy equivalence for finite-type locally constant étale module sheaves over a
finite ring commutes with inverse image and restriction along the induced fundamental-group
homomorphism. -/
@[stacks 0DV6] #check (AlgebraicGeometry.Scheme.finiteTypeLocallyConstantModule_pullback_lambda_catCommSq :
    ∀ {Y X : Scheme.{u}} (f : Y ⟶ X) (Λ : Type (u + 1)) [Ring Λ]
    [Finite Λ]
    [ConnectedSpace Y] [ConnectedSpace X]
    [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (ybar : GeometricPoint Y),
    Nonempty
      (CatCommSq (finiteTypeLocallyConstantModulePullback f Λ)
        (finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ
          (GeometricPoint.map ybar f)).functor
        (finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ ybar).functor
        (etaleFundamentalGroupMap_resFiniteTypeDiscreteModule f Λ ybar)))

/- Remark 59.65.3 (4): On irreducible geometrically unibranch schemes, the monodromy equivalence for finite-type
locally constant étale module sheaves over an arbitrary ring commutes with inverse image and
restriction along the induced fundamental-group homomorphism. -/
@[stacks 0DV6] #check (AlgebraicGeometry.Scheme.finiteTypeLocallyConstantModule_pullback_catCommSq :
    ∀ {Y X : Scheme.{u}} (f : Y ⟶ X) (Λ : Type (u + 1)) [Ring Λ]
    [ConnectedSpace Y] [ConnectedSpace X]
    [IrreducibleSpace Y] [IrreducibleSpace X]
    (huniY : Y.isGeometricallyUnibranch) (huniX : X.isGeometricallyUnibranch)
    [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (ybar : GeometricPoint Y),
    Nonempty
      (CatCommSq (finiteTypeLocallyConstantModulePullback f Λ)
        (finiteTypeLocallyConstantModule_equivalence_finitePi1Modules Λ huniX
          (GeometricPoint.map ybar f)).functor
        (finiteTypeLocallyConstantModule_equivalence_finitePi1Modules Λ huniY ybar).functor
        (etaleFundamentalGroupMap_resFiniteTypeDiscreteModule f Λ ybar)))
