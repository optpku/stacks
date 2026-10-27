/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CartesianSquare
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
variable (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
variable (ℱ : X.Modules) [ℱ.IsQuasicoherent]

/- 69.11.0.1: over a scheme `S`, a morphism `f : X ⟶ Y` of algebraic spaces, a
quasi-coherent `𝒪_X`-module `ℱ`, and a morphism `g : Y' ⟶ Y`, the fibre product
`X' = Y' ×_Y X` with projections `g' : X' ⟶ X` and `f' : X' ⟶ Y'` is cartesian,
and the diagram records `ℱ' = (g')^* ℱ` together with the derived pushforwards
`Rf'_* ℱ'` and `Rf_* ℱ`. -/
@[stacks 073J] #check (CategoryTheory.IsPullback g' f' f g : Prop)

#check (Modules.pullback :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Y.Modules ⥤ X.Modules)
#check (Modules.pushforward :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → X.Modules ⥤ Y.Modules)
#check CategoryTheory.Functor.rightDerived

#check ((Modules.pullback g').obj ℱ : X'.Modules)
