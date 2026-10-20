/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Inertia.Functoriality.NatTrans.Construction
public import ReasLib.CategoryTheory.Inertia.Functoriality.Comparison

/-!
# Whiskering and section naturality for inertia

This leaf owns the horizontal functoriality of the natural-transformation action, together with
its forgetful and identity-section naturality equations.
-/

@[expose] public section

open CategoryTheory

universe uC vC uD vD uE vE

namespace CategoryTheory
namespace Inertia

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {E : Type uE} [Category.{vE} E]

/-- The explicit inertia action on natural transformations is compatible with left
whiskering. The equality transports are supplied by strict preservation of functor
composition. -/
theorem map₂.whiskerLeft
    (F : C ⥤ D) {G H : D ⥤ E} (η : G ⟶ H) :
    map₂ (Functor.whiskerLeft F η) =
      eqToHom (map.comp F G) ≫
        Functor.whiskerLeft (map F) (map₂ η) ≫
          eqToHom (map.comp F H).symm := sorry

/-- The explicit inertia action on natural transformations is compatible with right
whiskering. The equality transports are supplied by strict preservation of functor
composition. -/
theorem map₂.whiskerRight
    {F G : C ⥤ D} (η : F ⟶ G) (H : D ⥤ E) :
    map₂ (Functor.whiskerRight η H) =
      eqToHom (map.comp F H) ≫
        Functor.whiskerRight (map₂ η) (map H) ≫
          eqToHom (map.comp G H).symm := sorry

/-- Forgetting automorphisms is 2-natural with respect to a natural transformation. -/
theorem map₂.whiskerRight.forget {F G : C ⥤ D} (η : F ⟶ G) :
    Functor.whiskerRight (map₂ η) (forget D) =
      Functor.whiskerLeft (forget C) η := sorry

/-- Mapping identity-automorphism objects agrees with first applying the original functor and
then taking the identity-automorphism object. -/
@[simp]
theorem identitySection.comp_map (F : C ⥤ D) :
    identitySection C ⋙ map F = F ⋙ identitySection D := sorry

/-- The identity-automorphism section is 2-natural with respect to a natural
transformation. The equality transports are exactly those supplied by
identitySection.comp_map. -/
theorem map₂.identitySection.naturality {F G : C ⥤ D} (η : F ⟶ G) :
    Functor.whiskerLeft (identitySection C) (map₂ η) =
      eqToHom (identitySection.comp_map F) ≫
        Functor.whiskerRight η (identitySection D) ≫
          eqToHom (identitySection.comp_map G).symm := sorry

end Inertia
end CategoryTheory
