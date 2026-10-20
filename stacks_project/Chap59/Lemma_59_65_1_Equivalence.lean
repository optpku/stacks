/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.Equivalence
public import stacks_project.Chap59.Lemma_59_65_1_Forward
public import stacks_project.Chap59.Lemma_59_65_1_StalkComparison

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

#check (AlgebraicGeometry.Scheme.finiteLocallyConstantAddCommGrp_equivalence_finitePi1Modules :
  {X : Scheme.{u}} → [ConnectedSpace X] → (xbar : GeometricPoint X) →
  [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))] →
  [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))] →
  [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}] →
  [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{u + 1}] →
  (Sheaf.finiteLocallyConstantAddCommGrp X.smallEtaleTopology).FullSubcategory ≌
    (finiteDiscreteModule ℤ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory)
