/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LocallyConstantPullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.Equivalence
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteTypeMonodromy
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FundamentalGroup

@[expose] public section

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Action.ModuleCat
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {Y X : Scheme.{u}} (f : Y ⟶ X)
variable (Λ : Type (u + 1)) [Ring Λ]

/-- Restriction of finite discrete `π₁`-modules along the continuous homomorphism induced by `f`. -/
noncomputable def etaleFundamentalGroupMap_resFiniteDiscreteModule
    [ConnectedSpace Y] [ConnectedSpace X] (ybar : GeometricPoint Y) :
    (finiteDiscreteModule ℤ
      (Aut (GeometricPoint.finiteFiber (GeometricPoint.map ybar f)))).FullSubcategory ⥤
      (finiteDiscreteModule ℤ (Aut (GeometricPoint.finiteFiber ybar))).FullSubcategory :=
  (finiteDiscreteModule ℤ (Aut (GeometricPoint.finiteFiber ybar))).lift
    ((finiteDiscreteModule ℤ
        (Aut (GeometricPoint.finiteFiber (GeometricPoint.map ybar f)))).ι ⋙
      discreteModuleRes (GeometricPoint.fundamentalGroupMap f ybar))
    fun M ↦ M.property

/-- Restriction of finite-type discrete `π₁`-modules along the continuous homomorphism
induced by `f`. -/
noncomputable def etaleFundamentalGroupMap_resFiniteTypeDiscreteModule
    [ConnectedSpace Y] [ConnectedSpace X] (ybar : GeometricPoint Y) :
    (finiteTypeDiscreteModule Λ
      (Aut (GeometricPoint.finiteFiber (GeometricPoint.map ybar f)))).FullSubcategory ⥤
      (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber ybar))).FullSubcategory :=
  (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber ybar))).lift
    ((finiteTypeDiscreteModule Λ
        (Aut (GeometricPoint.finiteFiber (GeometricPoint.map ybar f)))).ι ⋙
      discreteModuleRes (GeometricPoint.fundamentalGroupMap f ybar))
    fun M ↦ M.property

/-- The monodromy equivalence for finite locally constant étale sheaves of sets commutes
with inverse image and restriction along the induced fundamental-group homomorphism. -/
theorem finiteLocallyConstant_pullback_catCommSq
    [ConnectedSpace Y] [ConnectedSpace X]
    [HasWeakSheafify Y.smallEtaleTopology (Type (u + 1))]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (Type (u + 1))]
    [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))]
    [∀ P : X.Etaleᵒᵖ ⥤ Type (u + 1), (smallEtalePullback f).op.HasLeftKanExtension P]
    (ybar : GeometricPoint Y) :
    Nonempty
      (CatCommSq (finiteLocallyConstantPullback f)
        (finiteLocallyConstant_equivalence_finitePi1Sets
          (GeometricPoint.map ybar f)).functor
        (finiteLocallyConstant_equivalence_finitePi1Sets ybar).functor
        (GeometricPoint.fundamentalGroupRestriction f ybar)) :=
  sorry

/-- The monodromy equivalence for finite locally constant étale sheaves of abelian groups
commutes with inverse image and restriction along the induced fundamental-group homomorphism. -/
theorem finiteLocallyConstantAddCommGrp_pullback_catCommSq
    [ConnectedSpace Y] [ConnectedSpace X]
    [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}]
    [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (ybar : GeometricPoint Y) :
    Nonempty
      (CatCommSq (finiteLocallyConstantAddCommGrpPullback f)
        (finiteLocallyConstantAddCommGrp_equivalence_finitePi1Modules
          (GeometricPoint.map ybar f)).functor
        (finiteLocallyConstantAddCommGrp_equivalence_finitePi1Modules ybar).functor
        (etaleFundamentalGroupMap_resFiniteDiscreteModule f ybar)) :=
  sorry

/-- The monodromy equivalence for finite-type locally constant étale module sheaves over a
finite ring commutes with inverse image and restriction along the induced fundamental-group
homomorphism. -/
theorem finiteTypeLocallyConstantModule_pullback_lambda_catCommSq
    [Finite Λ]
    [ConnectedSpace Y] [ConnectedSpace X]
    [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (ybar : GeometricPoint Y) :
    Nonempty
      (CatCommSq (finiteTypeLocallyConstantModulePullback f Λ)
        (finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ
          (GeometricPoint.map ybar f)).functor
        (finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules Λ ybar).functor
        (etaleFundamentalGroupMap_resFiniteTypeDiscreteModule f Λ ybar)) :=
  sorry

/-- On irreducible geometrically unibranch schemes, the monodromy equivalence for finite-type
locally constant étale module sheaves over an arbitrary ring commutes with inverse image and
restriction along the induced fundamental-group homomorphism. -/
theorem finiteTypeLocallyConstantModule_pullback_catCommSq
    [ConnectedSpace Y] [ConnectedSpace X]
    [IrreducibleSpace Y] [IrreducibleSpace X]
    (huniY : Y.isGeometricallyUnibranch) (huniX : X.isGeometricallyUnibranch)
    [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P]
    (ybar : GeometricPoint Y) :
    Nonempty
      (CatCommSq (finiteTypeLocallyConstantModulePullback f Λ)
        (finiteTypeLocallyConstantModule_equivalence_finitePi1Modules Λ huniX
          (GeometricPoint.map ybar f)).functor
        (finiteTypeLocallyConstantModule_equivalence_finitePi1Modules Λ huniY ybar).functor
        (etaleFundamentalGroupMap_resFiniteTypeDiscreteModule f Λ ybar)) :=
  sorry

end AlgebraicGeometry.Scheme
