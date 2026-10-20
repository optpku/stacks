/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.EnoughNegativeObjects

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

/- An abelian category has enough negative objects when every object admits an
epimorphism from an object receiving only zero maps from it. -/
#check (CategoryTheory.HasEnoughNegativeObjects :
  ∀ (C : Type u) [Category.{v} C] [Abelian C], Prop)
