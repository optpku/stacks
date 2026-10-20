/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.FiniteLocallyConstant.ModuleSheafInverse
public import stacks_project.Chap59.Lemma_59_65_1_Forward
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.Data.Fintype.Shrink
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Limits.Yoneda

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

#check (AlgebraicGeometry.Scheme.ModuleSheafInverse.functor :
  (Λ : Type v) → [Ring Λ] → {X : Scheme.{u}} → [ConnectedSpace X] →
  (xbar : GeometricPoint X) →
  [HasWeakSheafify X.smallEtaleTopology (Type (u + 1))] →
  [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (Type (u + 1))] →
  [Finite Λ] →
  (finiteTypeDiscreteModule Λ (Aut (GeometricPoint.finiteFiber xbar))).FullSubcategory ⥤
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
