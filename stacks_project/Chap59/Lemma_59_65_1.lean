/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap59.Lemma_59_65_1_Equivalence
public import stacks_project.Chap59.Lemma_59_65_1_StalkRepresentation
public import stacks_project.Chap59.Lemma_59_65_1_Forward
public import stacks_project.Chap59.Lemma_59_65_1_ModuleSheafInverse
public import stacks_project.Chap59.Lemma_59_65_1_StalkComparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped FintypeCatDiscrete

universe u

/- Lemma 59.65.1 (1): finite locally constant sheaves of sets on the small étale site of a
connected scheme `X` are equivalent to finite `π₁(X, x̄)`-sets. -/
@[stacks 0DV5]
#check (AlgebraicGeometry.Scheme.finiteLocallyConstant_equivalence_finitePi1Sets :
  {X : Scheme.{u}} →
  [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))] →
  [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))] →
  [ConnectedSpace X] → (xbar : GeometricPoint X) →
  (Sheaf.finiteLocallyConstant X.smallEtaleTopology).FullSubcategory ≌
    ContAction FintypeCat.{u} (Aut (GeometricPoint.finiteFiber xbar)))

/- Lemma 59.65.1 (2): finite locally constant sheaves of abelian groups on the small étale site
of a connected scheme `X` are equivalent to finite `π₁(X, x̄)`-modules. -/
@[stacks 0DV5]
#check (AlgebraicGeometry.Scheme.finiteLocallyConstantAddCommGrp_equivalence_finitePi1Modules :
  {X : Scheme.{u}} → [ConnectedSpace X] → (xbar : GeometricPoint X) →
  [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))] →
  [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))] →
  [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}] →
  [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}] →
  (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory ≌
    (finiteDiscreteModule ℤ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory)

/- Lemma 59.65.1 (3): for a finite ring `Λ`, finite-type locally constant sheaves of `Λ`-modules
on the small étale site of a connected scheme `X` are equivalent to finite `π₁(X, x̄)`-modules
with a commuting `Λ`-module structure. -/
@[stacks 0DV5]
#check (AlgebraicGeometry.Scheme.finiteTypeLocallyConstantModule_equivalence_finitePi1LambdaModules :
  {X : Scheme.{u}} → (Λ : Type (u + 1)) → [Ring Λ] → [Finite Λ] →
  [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)] →
  [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)] →
  [ConnectedSpace X] → (xbar : GeometricPoint X) →
  (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory ≌
    (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory)
