/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Computation for Localization Liftings

The comparison isomorphism of a `Localization.Lifting` determines the value of the lifted
functor on every morphism coming from the localization functor.  This leaf names both naturality
directions and the resulting conjugation formula so downstream APIs do not repeat the same
equations for each localization model.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

namespace Localization.Lifting

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

namespace iso

/-- Naturality of the forward comparison isomorphism for a localization lifting. -/
@[reassoc (attr := simp), stacks 05SE "forward localization-lifting computation"]
theorem hom_naturality {L : C ⥤ D} {W : MorphismProperty C}
    {F : C ⥤ E} {F' : D ⥤ E} [Localization.Lifting L W F F']
    {X Y : C} (f : X ⟶ Y) :
    F'.map (L.map f) ≫ (Localization.Lifting.iso L W F F').hom.app Y =
      (Localization.Lifting.iso L W F F').hom.app X ≫ F.map f := sorry

/-- Naturality of the inverse comparison isomorphism for a localization lifting. -/
@[reassoc (attr := simp), stacks 05SE "inverse localization-lifting computation"]
theorem inv_naturality {L : C ⥤ D} {W : MorphismProperty C}
    {F : C ⥤ E} {F' : D ⥤ E} [Localization.Lifting L W F F']
    {X Y : C} (f : X ⟶ Y) :
    F.map f ≫ (Localization.Lifting.iso L W F F').inv.app Y =
      (Localization.Lifting.iso L W F F').inv.app X ≫ F'.map (L.map f) := sorry

end iso

/-- A lifted functor maps a morphism from the localization functor by conjugating its original
image with the canonical lifting comparison. -/
@[reassoc, stacks 05SE "map computation for a localization lifting"]
theorem map_localization {L : C ⥤ D} {W : MorphismProperty C}
    {F : C ⥤ E} {F' : D ⥤ E} [Localization.Lifting L W F F']
    {X Y : C} (f : X ⟶ Y) :
    F'.map (L.map f) =
      (iso L W F F').hom.app X ≫ F.map f ≫ (iso L W F F').inv.app Y := sorry

end Localization.Lifting


end CategoryTheory
