/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Whiskering
public import stacks_project.Chap78.«78_19_0_1_QuotientPresheaf»
public import stacks_project.Chap78.Lemma_78_11_2_Groupoid
public import stacks_project.Chap78.Lemma_78_15_1_Action
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action.QuotientSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf

/-!
# Compatibility names for universe-raised algebraic-space sheaves

This module retains the `uliftSheaf` and `uliftSheafMap` compatibility names for the
canonical universe-raised fppf sheaf functor `AlgebraicSpace.toSheaf`. Quotient sheaves,
quotient classes, and their canonical morphisms are supplied by the shared imports.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Universe-raised functor of points of an algebraic space is an fppf sheaf. -/
theorem uliftSheaf_isSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (X.functorOfPoints ⋙ uliftFunctor.{u + 1, u}) :=
  toSheaf_isSheaf X

/-- The universe-raised fppf sheaf of points of an algebraic space. -/
abbrev uliftSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  toSheaf.obj X

/-- The underlying presheaf of `uliftSheaf X` is the universe-raised functor of points. -/
theorem uliftSheaf_obj {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (uliftSheaf X).obj = X.functorOfPoints ⋙ uliftFunctor.{u + 1, u} :=
  toSheaf_obj X

/-- The sheaf morphism induced by a morphism of algebraic spaces. -/
abbrev uliftSheafMap {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    uliftSheaf X ⟶ uliftSheaf Y :=
  toSheaf.map f

/-- The underlying presheaf morphism of `uliftSheafMap f` is universe-raising of `f`. -/
theorem uliftSheafMap_hom {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (uliftSheafMap f).hom = Functor.whiskerRight f uliftFunctor.{u + 1, u} :=
  toSheaf_map f

end AlgebraicGeometry.AlgebraicSpace
