/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Constant
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FinitePresentation
public import ReasLib.CategoryTheory.Sites.SheafTheoreticEmpty.Nonempty
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finiteness of constant module sheaves

On a site with nonempty sheaf topos, finite type and finite presentation of a
constant module sheaf are equivalent to the corresponding algebraic
properties of its value module.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Type w} [Ring R]
variable [HasWeakSheafify J RingCat.{w}]
variable [J.WEqualsLocallyBijective RingCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify J (ModuleCat.{w} R)]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Lemma 18.42.5 (093N) (1): a constant `R`-module sheaf is of finite type
exactly when its value module is finite, provided the sheaf topos is
nonempty. -/
@[stacks 093N "(1)"]
theorem constant_isFiniteType_iff
    (M : ModuleCat.{w} R) (hJ : J.HasNonemptySheafTopos) :
    (((constantSheaf J (ModuleCat.{w} R)).obj M).toConstantModuleSheaf).IsFiniteType ↔
      Module.Finite R M := sorry

/-- Lemma 18.42.5 (093N) (2): a constant `R`-module sheaf is finitely
presented exactly when its value module is finitely presented, provided the
sheaf topos is nonempty. -/
@[stacks 093N "(2)"]
theorem constant_isFinitePresentation_iff
    (M : ModuleCat.{w} R) (hJ : J.HasNonemptySheafTopos) :
    (((constantSheaf J (ModuleCat.{w} R)).obj M).toConstantModuleSheaf).IsFinitePresentation ↔
      Module.FinitePresentation R M := sorry

end CategoryTheory.Sheaf
