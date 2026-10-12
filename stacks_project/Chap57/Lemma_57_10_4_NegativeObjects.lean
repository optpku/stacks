/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
