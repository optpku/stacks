/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic

/-!
# Everywhere-defined total derived functors

An everywhere-defined derived functor yields a total derived functor on any
localization model, together with its canonical comparison transformation.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  (F : C ⥤ D) (S : MorphismProperty C) (L : C ⥤ E) [L.IsLocalization S]

namespace RightDerived.EverywhereDefined

variable [RightDerived.EverywhereDefined F S]

/-- The total right-derived functor of an everywhere-defined functor on a localization. -/
noncomputable def functor : E ⥤ D := F.totalRightDerived L S

/-- The canonical comparison from a functor to its total right-derived functor
precomposed with localization. -/
noncomputable def unit : F ⟶ L ⋙ functor F S L := F.totalRightDerivedUnit L S

/-- The canonical comparison exhibits the total right-derived functor as a right-derived
functor relative to the given morphism property. -/
noncomputable instance isRightDerivedFunctor :
    (functor F S L).IsRightDerivedFunctor (unit F S L) S :=
  inferInstanceAs ((F.totalRightDerived L S).IsRightDerivedFunctor
    (F.totalRightDerivedUnit L S) S)

end RightDerived.EverywhereDefined

namespace LeftDerived.EverywhereDefined

variable [LeftDerived.EverywhereDefined F S]

/-- The total left-derived functor of an everywhere-defined functor on a localization. -/
noncomputable def functor : E ⥤ D := F.totalLeftDerived L S

/-- The canonical comparison from the total left-derived functor precomposed with
localization to the original functor. -/
noncomputable def counit : L ⋙ functor F S L ⟶ F := F.totalLeftDerivedCounit L S

/-- The canonical comparison exhibits the total left-derived functor as a left-derived
functor relative to the given morphism property. -/
noncomputable instance isLeftDerivedFunctor :
    (functor F S L).IsLeftDerivedFunctor (counit F S L) S :=
  inferInstanceAs ((F.totalLeftDerived L S).IsLeftDerivedFunctor
    (F.totalLeftDerivedCounit L S) S)

end LeftDerived.EverywhereDefined

end CategoryTheory.Functor
