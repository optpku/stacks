/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiniteLocallyFree
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 67.46.2 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`
is finite locally free if it is affine and `f_* 𝒪_X` is a finite locally free `𝒪_Y`-module. -/
@[stacks 03ZV] #check (AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFree :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

/- Definition 67.46.2 (2): a finite locally free morphism `f : X ⟶ Y` of algebraic spaces
over a scheme `S` has rank or degree `d` if `f_* 𝒪_X` is finite locally free of rank `d`. -/
@[stacks 03ZV] #check (AlgebraicGeometry.AlgebraicSpace.FiniteLocallyFreeOfRank :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → ℕ → Prop)
