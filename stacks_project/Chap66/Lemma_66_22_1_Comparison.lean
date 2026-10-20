/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.CategoryTheory.Limits.Over.Products
public import stacks_project.Chap66.Definition_66_19_6_Neighborhood
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing
public import stacks_project.Chap66.Lemma_66_18_8_Representable
public import stacks_project.Chap66.Lemma_66_18_12_Restriction

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Neighborhood

/-!
# Comparison of étale local rings along a scheme étale neighbourhood

The canonical comparison identifies an algebraic-space étale stalk with the stalk of a
scheme étale neighbourhood at its induced geometric point.
-/

open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.etaleLocalRing_etaleNeighborhood :
  {S : Scheme.{u}} → {X : AlgebraicSpace S} →
    {xbar : AlgebraicSpace.GeometricPoint X} →
    (N : AlgebraicSpace.GeometricPoint.SmallEtaleNeighborhood xbar) →
    AlgebraicSpace.etaleLocalRing X xbar ≃+*
      Scheme.etaleLocalRing N.scheme
        (AlgebraicSpace.GeometricPoint.SmallEtaleNeighborhood.schemeGeometricPoint N))
