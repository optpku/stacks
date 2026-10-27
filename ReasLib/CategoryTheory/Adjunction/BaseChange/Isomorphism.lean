/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Adjunction.BaseChange

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedBaseChange

/-- A right-square isomorphism has invertible inverse mate when the source unit
and target counit are invertible. Without these hypotheses the assertion is false:
for the empty-set adjunctions from the terminal category to `Type`, the identity
right square with constant-singleton vertical functor has mate `Empty → PUnit`. -/
theorem mapOfRight_isIso
    {C D C' D' : Type u} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {L' : C' ⥤ D'} {R : D ⥤ C} {R' : D' ⥤ C'}
    {G : C ⥤ C'} {H : D ⥤ D'} (adj : L ⊣ R) (adj' : L' ⊣ R')
    (square : R ⋙ G ⟶ H ⋙ R') [IsIso square]
    [IsIso adj.unit] [IsIso adj'.counit] :
    IsIso (mapOfRight adj adj' square) := by
  dsimp [mapOfRight, mateEquiv]
  infer_instance

end CategoryTheory.DerivedBaseChange

