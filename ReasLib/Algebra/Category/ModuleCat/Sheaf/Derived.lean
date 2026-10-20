/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The standard unbounded derived category of sheaves of modules over a ring sheaf. -/
noncomputable instance hasDerivedCategory
    (𝒪 : Sheaf J RingCat.{u})
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [IsGrothendieckAbelian.{w} (SheafOfModules.{w} 𝒪)] :
    HasDerivedCategory (SheafOfModules.{w} 𝒪) :=
  HasDerivedCategory.standard _

end SheafOfModules

end
