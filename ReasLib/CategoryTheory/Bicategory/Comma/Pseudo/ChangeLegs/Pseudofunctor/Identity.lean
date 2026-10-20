/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo.ChangeLegs.Basic

/-!
# Identity comparison for changing pseudo comma legs

The change-of-legs action preserves endpoint maps. Its identity comparison is
therefore lifted from the two reflexivity isomorphisms by `PseudoComma.isoMk`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe wA vA uA wB vB uB wC vC uC

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]

namespace PseudoComma

variable {F F' : A ⥤ᵖ C} {G G' : B ⥤ᵖ C}

namespace Implementation

/-- The left endpoint comparison for the identity constraint of changing
pseudo comma legs. -/
private noncomputable def mapId.leftIso
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    (S : PseudoComma F G) :
    left (F := F') (G := G') (changeLegs.map α β (𝟙 S)) ≅
      left (F := F') (G := G')
        ((𝟙 (changeLegs.obj α β S)) :
          changeLegs.obj α β S ⟶ changeLegs.obj α β S) :=
  Iso.refl _

/-- The right endpoint comparison for the identity constraint of changing
pseudo comma legs. -/
private noncomputable def mapId.rightIso
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    (S : PseudoComma F G) :
    right (F := F') (G := G') (changeLegs.map α β (𝟙 S)) ≅
      right (F := F') (G := G')
        ((𝟙 (changeLegs.obj α β S)) :
          changeLegs.obj α β S ⟶ changeLegs.obj α β S) :=
  Iso.refl _

/-- Compatibility of the identity endpoint comparisons with the changed
pseudo comma structural cells. -/
private theorem mapId.w
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    (S : PseudoComma F G) :
    (F'.map₂ (mapId.leftIso α β S).hom ▷
        ColaxComma.hom (changeLegs.obj α β S)) ≫
        cell (F := F') (G := G')
          ((𝟙 (changeLegs.obj α β S)) :
            changeLegs.obj α β S ⟶ changeLegs.obj α β S) =
      cell (F := F') (G := G') (changeLegs.map α β (𝟙 S)) ≫
        (ColaxComma.hom (changeLegs.obj α β S) ◁
          G'.map₂ (mapId.rightIso α β S).hom) := sorry

end Implementation

/-- The identity comparison for changing two pseudo comma legs. -/
noncomputable def changeLegs.mapId
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    (S : PseudoComma F G) :
    changeLegs.map α β (𝟙 S) ≅ 𝟙 (changeLegs.obj α β S) :=
  isoMk (Implementation.mapId.leftIso α β S)
    (Implementation.mapId.rightIso α β S)
    (Implementation.mapId.w α β S)

/- Data and axiom audit (mathlib 4.32):

`changeLegs.mapId` uses the explicit identity endpoint isomorphisms. Its only
deferred content is their `Prop`-valued pseudo comma compatibility. -/

end PseudoComma

end Bicategory

end CategoryTheory
