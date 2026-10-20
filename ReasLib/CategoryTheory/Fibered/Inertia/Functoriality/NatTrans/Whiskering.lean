/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.NatTrans.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Comparison.IdentityComposition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Whiskering laws for the local based-inertia action

This leaf owns horizontal functoriality and the forgetful and identity-section `2`-naturality
equations for the explicit based-inertia action.
-/

@[expose] public section

universe u v u₁ v₁ u₂ v₂ u₃ v₃

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans
open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace Inertia.map₂

variable {X : BasedCategory.{v₁, u₁} C}
variable {Y : BasedCategory.{v₂, u₂} C}
variable {Z : BasedCategory.{v₃, u₃} C}
variable {F G : X ⥤ᵇ Y}

/-- The inertia action is compatible with left whiskering. -/
@[stacks 04Z4 "based inertia two-cell left whiskering"]
theorem whiskerLeft
    (F : X ⥤ᵇ Y) {G H : Y ⥤ᵇ Z} (η : G ⟶ H) :
    Inertia.map₂ (BasedCategory.whiskerLeft F η) =
      eqToHom (Inertia.map.comp F G) ≫
        BasedCategory.whiskerLeft (Inertia.map F) (Inertia.map₂ η) ≫
          eqToHom (Inertia.map.comp F H).symm := sorry

/-- The inertia action is compatible with right whiskering. -/
@[stacks 04Z4 "based inertia two-cell right whiskering"]
theorem whiskerRight
    {F G : X ⥤ᵇ Y} (η : F ⟶ G) (H : Y ⥤ᵇ Z) :
    Inertia.map₂ (BasedCategory.whiskerRight η H) =
      eqToHom (Inertia.map.comp F H) ≫
        BasedCategory.whiskerRight (Inertia.map₂ η) (Inertia.map H) ≫
          eqToHom (Inertia.map.comp G H).symm := sorry

/-- Forgetting automorphisms is `2`-natural for inertia. -/
@[stacks 04Z4 "based inertia forgetful two-naturality"]
theorem whiskerRight.forget (η : F ⟶ G) :
    BasedCategory.whiskerRight (Inertia.map₂ η) (Inertia.forget Y) =
      eqToHom (Inertia.map.comp_forget F) ≫
        BasedCategory.whiskerLeft (Inertia.forget X) η ≫
          eqToHom (Inertia.map.comp_forget G).symm := sorry

/-- The identity-automorphism section is `2`-natural for inertia. -/
@[stacks 04Z4 "based inertia identity-section two-naturality"]
theorem identitySection.naturality (η : F ⟶ G) :
    BasedCategory.whiskerLeft (Inertia.identitySection X) (Inertia.map₂ η) =
      eqToHom (Inertia.identitySection.comp_map F) ≫
        BasedCategory.whiskerRight η (Inertia.identitySection Y) ≫
          eqToHom (Inertia.identitySection.comp_map G).symm := sorry

end Inertia.map₂

end BasedCategory
end CategoryTheory
