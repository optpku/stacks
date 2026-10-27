/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import stacks_project.Chap99.Lemma_99_16_4
public import stacks_project.Chap110.Lemma_110_53_1

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.StructureMorphism

/-!
# Structure morphism of the stack of complexes

Typed compatibility checks exposing the shared structure morphism to existing
consumers of this module and its historical chart vocabulary.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupScheme
open scoped Bicategory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Complexes.toSchemesOver :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f],
    AlgebraicGeometry.AlgebraicSpace.Complexes.category f ⥤ SchemeOver B)

#check (AlgebraicGeometry.AlgebraicSpace.Complexes.toBase :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    [Proper f] [Flat f] [FinitePresentation f],
    AlgebraicGeometry.AlgebraicSpace.Complexes.toGroupoids f ⟶ Classifying.toGroupoids B)
