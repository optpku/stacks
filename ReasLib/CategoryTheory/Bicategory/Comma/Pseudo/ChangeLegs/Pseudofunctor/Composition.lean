module

public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo.ChangeLegs.Basic

/-!
# Composition comparison for changing pseudo comma legs

The change-of-legs action preserves endpoint maps. Its composition comparison
is therefore lifted from the two reflexivity isomorphisms by
`PseudoComma.isoMk`.
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

/-- The left endpoint comparison for the composition constraint of changing
pseudo comma legs. -/
private noncomputable def mapComp.leftIso
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    {S T U : PseudoComma F G} (u : S ⟶ T) (v : T ⟶ U) :
    left (F := F') (G := G') (changeLegs.map α β (u ≫ v)) ≅
      left (F := F') (G := G')
        (changeLegs.map α β u ≫ changeLegs.map α β v) :=
  Iso.refl _

/-- The right endpoint comparison for the composition constraint of changing
pseudo comma legs. -/
private noncomputable def mapComp.rightIso
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    {S T U : PseudoComma F G} (u : S ⟶ T) (v : T ⟶ U) :
    right (F := F') (G := G') (changeLegs.map α β (u ≫ v)) ≅
      right (F := F') (G := G')
        (changeLegs.map α β u ≫ changeLegs.map α β v) :=
  Iso.refl _

/-- Compatibility of the composition endpoint comparisons with the changed
pseudo comma structural cells. -/
private theorem mapComp.w
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    {S T U : PseudoComma F G} (u : S ⟶ T) (v : T ⟶ U) :
    (F'.map₂ (mapComp.leftIso α β u v).hom ▷
        ColaxComma.hom (changeLegs.obj α β U)) ≫
        cell (F := F') (G := G')
          (changeLegs.map α β u ≫ changeLegs.map α β v) =
      cell (F := F') (G := G') (changeLegs.map α β (u ≫ v)) ≫
        (ColaxComma.hom (changeLegs.obj α β S) ◁
          G'.map₂ (mapComp.rightIso α β u v).hom) := sorry

end Implementation

/-- The composition comparison for changing two pseudo comma legs. -/
noncomputable def changeLegs.mapComp
    (α : Pseudofunctor.StrongTrans F' F)
    (β : Pseudofunctor.StrongTrans G G')
    {S T U : PseudoComma F G} (u : S ⟶ T) (v : T ⟶ U) :
    changeLegs.map α β (u ≫ v) ≅
      changeLegs.map α β u ≫ changeLegs.map α β v :=
  isoMk (Implementation.mapComp.leftIso α β u v)
    (Implementation.mapComp.rightIso α β u v)
    (Implementation.mapComp.w α β u v)

/- Data and axiom audit (mathlib 4.32):

`changeLegs.mapComp` uses the explicit identity endpoint isomorphisms. Its only
deferred content is their `Prop`-valued pseudo comma compatibility. -/

end PseudoComma

end Bicategory

end CategoryTheory
