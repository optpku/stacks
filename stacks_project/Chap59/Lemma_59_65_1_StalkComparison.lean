/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.StalkComparison
public import stacks_project.Chap59.Lemma_59_65_1_FiniteCarrierInverse
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite.UnderlyingModule
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

#check (AlgebraicGeometry.Scheme.ModuleSheafInverse.equivalence :
  {X : Scheme.{u}} → [ConnectedSpace X] → (xbar : GeometricPoint X) →
  (Λ : Type (u + 1)) → [Ring Λ] → [Finite Λ] →
  [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))] →
  [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))] →
  [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)] →
  [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)] →
  (Sheaf.finiteTypeLocallyConstantModule X.smallEtaleTopology Λ).FullSubcategory ≌
    (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory)
