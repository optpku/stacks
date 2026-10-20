/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.Grp.CharacterModule

@[expose] public section

open CategoryTheory

universe u

/- Precomposition of additive characters as a bundled additive-group morphism. -/
#check (@CharacterModule.dualAddMap :
  {M N : AddCommGrpCat.{u}} → (M ⟶ N) →
    (AddCommGrpCat.of (CharacterModule N) ⟶
      AddCommGrpCat.of (CharacterModule M)))

/- Additive character duality as a contravariant functor. -/
#check (CharacterModule.addCommGrpFunctor :
  AddCommGrpCat.{u}ᵒᵖ ⥤ AddCommGrpCat.{u})
