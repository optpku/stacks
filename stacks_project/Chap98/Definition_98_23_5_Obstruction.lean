/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.NaiveObstructionTheory

/-! # Naive obstruction theories -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.GroupoidsOver DerivedCategory

universe u

#check (AlgebraicGeometry.GroupoidsOver.NaiveObstructionTheory :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] (X : GroupoidsOver S)
    [HasStrongRimSchlessinger X], Type (u + 1))

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X : GroupoidsOver S} [HasStrongRimSchlessinger X]

#check (NaiveObstructionTheory.obstructionModule :
  ∀ (𝒪 : NaiveObstructionTheory X) (ξ : ObjectOverAffineOpen X),
    ModuleCat.{u} ξ.carrier ⥤ ModuleCat.{u + 1} ξ.carrier)
