/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Perfect.StrictlyPerfect
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.Additive

@[expose] public section

/-!
# Local perfect models of module-sheaf complexes

This module defines restriction to slice sites and the local strictly-perfect model criterion
directly for a sheaf of rings.
-/

open CategoryTheory

noncomputable section

universe u v w z

namespace SheafOfModules.CochainComplex

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}

/-- Module sheaves over a sheaf of rings carry the canonical homology structure induced by their
abelian category. -/
noncomputable instance moduleCategoryWithHomology
    (R : Sheaf J RingCat.{w}) [HasSheafify J AddCommGrpCat.{z}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{z}] :
    CategoryWithHomology (SheafOfModules.{z} R) :=
  CategoryTheory.categoryWithHomology_of_abelian

/-- The restriction of module-sheaf complexes to the slice over an object. -/
noncomputable abbrev localizedRestrictionComplex (U : C) :
    _root_.CochainComplex (SheafOfModules.{z} R) ℤ ⥤
      _root_.CochainComplex (SheafOfModules.{z} (R.over U)) ℤ :=
  (SheafOfModules.pushforward.{z} (𝟙 (R.over U)) :
    SheafOfModules.{z} R ⥤ SheafOfModules.{z} (R.over U)).mapHomologicalComplex
      (ComplexShape.up ℤ)

section Model

variable [UnivLE.{max u v, w}]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

/-- Complexes admitting a strictly perfect quasi-isomorphic model. -/
def hasStrictlyPerfectModel :
    ObjectProperty (_root_.CochainComplex (SheafOfModules.{w} R) ℤ) :=
  fun E ↦ ∃ E' : _root_.CochainComplex (SheafOfModules.{w} R) ℤ,
    ∃ α : E' ⟶ E, IsStrictlyPerfect E' ∧ QuasiIso α

end Model

section Local

variable [UnivLE.{max u v, w}]
variable [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]

/-- Perfect complexes are locally quasi-isomorphic to strictly perfect complexes. -/
def perfect : ObjectProperty (_root_.CochainComplex (SheafOfModules.{w} R) ℤ) :=
  fun E ↦ ∀ U : C, ∃ T : J.Cover U, ∀ I : T.Arrow,
    hasStrictlyPerfectModel ((localizedRestrictionComplex (R := R) I.Y).obj E)

end Local

end SheafOfModules.CochainComplex
