/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.HomCongr
public import ReasLib.CategoryTheory.Bicategory.HomotopyCategory.Equivalence
public import ReasLib.CategoryTheory.Bicategory.HomotopyCategory.LocallyGroupoidal
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Fiber
public import stacks_project.Chap94.Definition_94_12_1_Representable

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids.Hom

/-!
# Morphisms between groupoid fibrations represented by algebraic spaces

The canonical Hom equivalence identifies homotopy classes of morphisms with morphisms
of the presenting algebraic spaces.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Bicategory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.toGroupoids.homEquiv :
  ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S} {X Y : GroupoidsOver S},
    (X ≌ F.toGroupoids) → (Y ≌ G.toGroupoids) →
      (Bicategory.HomotopyCategory.mk X ⟶ Bicategory.HomotopyCategory.mk Y) ≃ (F ⟶ G))
