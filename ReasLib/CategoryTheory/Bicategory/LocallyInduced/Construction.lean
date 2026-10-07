module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.HomProperty
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Locally induced bicategories

This file constructs the bicategory obtained by retaining selected `1`-morphisms of an ambient
bicategory while keeping all ambient `2`-morphisms between them. It owns the basic constructors,
the bicategory instance, and computation lemmas for ambient representatives.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

universe w v u u' w' v' u''

namespace Bicategory

variable {B : Type u'}

/-- `LocallyInducedBicategory C F Q` equips the object type `B` with the bicategory whose
`1`-morphisms are the ambient `1`-morphisms satisfying `Q`, and whose `2`-morphisms are all
ambient `2`-morphisms between them.

It is the two-dimensional analogue of `InducedWideCategory`: `F` chooses the ambient objects,
`Q` chooses the `1`-morphisms, and local fullness avoids imposing a redundant property on
`2`-morphisms.

This is deliberately a typeclass synonym, following mathlib's
`Bicategory.InducedBicategory`: the object labels remain definitionally equal to `B`, while the
parameters distinguish the selected hom categories and hence the bicategory instance. Replacing
it by a one-field structure would add an uninformative object projection at every use. -/
@[stacks 0040 "locally induced bicategory", nolint unusedArguments]
def LocallyInducedBicategory
    (C : Type u) [Bicategory.{w, v} C]
    (F : B → C) (Q : HomProperty F) [Q.IsMultiplicative] :=
  B

namespace LocallyInducedBicategory

variable {C : Type u} [Bicategory.{w, v} C] {F : B → C}
  {Q : HomProperty F} [Q.IsMultiplicative]

/-- Coerce an object of a locally induced bicategory through its ambient
object family, as for mathlib's `InducedBicategory`. -/
instance hasCoeToSort {α : Sort*} [CoeSort C α] :
    CoeSort (LocallyInducedBicategory C F Q) α :=
  ⟨fun X ↦ F X⟩

/-- The induced category structure on objects and selected `1`-morphisms. -/
instance categoryStruct : CategoryStruct (LocallyInducedBicategory C F Q) where
  Hom X Y := (Q X Y).FullSubcategory
  id X := ⟨𝟙 (F X), Q.id_mem X⟩
  comp f g := ⟨f.obj ≫ g.obj, Q.comp_mem f.property g.property⟩

/-- Build a selected `1`-morphism from an ambient `1`-morphism satisfying the hom property. -/
@[stacks 0040 "selected morphism of a locally induced bicategory"]
abbrev mkHom {X Y : LocallyInducedBicategory C F Q}
    (f : F X ⟶ F Y) (hf : Q X Y f) : X ⟶ Y :=
  ⟨f, hf⟩

/-- The ambient `1`-morphism underlying `mkHom f hf` is `f`. -/
@[simp]
theorem mkHom.toAmbient {X Y : LocallyInducedBicategory C F Q}
    (f : F X ⟶ F Y) (hf : Q X Y f) :
    (mkHom f hf).obj = f := sorry
/- Proof strategy: the object projection of the subtype constructor is definitionally `f`. -/

section Construction

/-- The local hom-category pin used while assembling the locally induced bicategory. -/
-- Local instance justification (defeq pin): the bicategory fields below must use the
-- full-subcategory hom structure selected by `categoryStruct` definitionally.
local instance
    (X Y : LocallyInducedBicategory C F Q) : Category (X ⟶ Y) :=
  inferInstanceAs (Category (Q X Y).FullSubcategory)

/-- The underlying ambient `1`-morphism of an induced identity is the ambient identity. -/
@[simp]
lemma id.toAmbient (X : LocallyInducedBicategory C F Q) :
    (𝟙 X : X ⟶ X).obj = 𝟙 (F X) := sorry
/- Proof strategy: unfold `categoryStruct`; the identity is the selected ambient identity by
definition. -/

/-- The underlying ambient `1`-morphism of an induced composite is the ambient composite. -/
@[simp]
lemma comp.toAmbient {X Y Z : LocallyInducedBicategory C F Q}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g : X ⟶ Z).obj = f.obj ≫ g.obj := sorry
/- Proof strategy: unfold `categoryStruct`; the composite is the selected ambient composite by
definition. -/

/-- The underlying ambient `2`-morphism of an identity is the ambient identity. -/
@[simp]
lemma id₂.toAmbient {X Y : LocallyInducedBicategory C F Q} (f : X ⟶ Y) :
    (𝟙 f : f ⟶ f).hom = 𝟙 f.obj := sorry
/- Proof strategy: unfold the full-subcategory hom category; its identity cell is the ambient
identity cell. -/

/-- The underlying ambient `2`-morphism of a vertical composite is the ambient composite. -/
@[simp]
lemma comp₂.toAmbient {X Y : LocallyInducedBicategory C F Q}
    {f g h : X ⟶ Y} (η : f ⟶ g) (θ : g ⟶ h) :
    (η ≫ θ).hom = η.hom ≫ θ.hom := sorry
/- Proof strategy: unfold the full-subcategory hom category; vertical composition is inherited
from the ambient hom-category. -/

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- Left whiskering of selected `1`-morphisms and ambient `2`-morphisms. -/
private def whiskerLeft {X Y Z : LocallyInducedBicategory C F Q}
    (f : X ⟶ Y) {g h : Y ⟶ Z} (η : g ⟶ h) :
    f ≫ g ⟶ f ≫ h :=
  ObjectProperty.homMk (f.obj ◁ η.hom)

/-- Right whiskering of ambient `2`-morphisms by selected `1`-morphisms. -/
private def whiskerRight {X Y Z : LocallyInducedBicategory C F Q}
    {f g : X ⟶ Y} (η : f ⟶ g) (h : Y ⟶ Z) :
    f ≫ h ⟶ g ≫ h :=
  ObjectProperty.homMk (η.hom ▷ h.obj)

/-- The associator inherited from the ambient bicategory. -/
private def associator {W X Y Z : LocallyInducedBicategory C F Q}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ≫ g) ≫ h ≅ f ≫ (g ≫ h) :=
  (Q _ _).isoMk (α_ f.obj g.obj h.obj)

/-- The left unitor inherited from the ambient bicategory. -/
private def leftUnitor {X Y : LocallyInducedBicategory C F Q} (f : X ⟶ Y) :
    𝟙 X ≫ f ≅ f :=
  (Q _ _).isoMk (λ_ f.obj)

/-- The right unitor inherited from the ambient bicategory. -/
private def rightUnitor {X Y : LocallyInducedBicategory C F Q} (f : X ⟶ Y) :
    f ≫ 𝟙 Y ≅ f :=
  (Q _ _).isoMk (ρ_ f.obj)

/-- Left whiskering preserves identity `2`-morphisms. -/
private theorem whiskerLeftId {X Y Z : LocallyInducedBicategory C F Q}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    whiskerLeft f (𝟙 g) = 𝟙 (f ≫ g) := sorry
/- Proof strategy: apply `ObjectProperty.hom_ext`; the ambient equation is
`CategoryTheory.Bicategory.whiskerLeft_id f.obj g.obj`. -/

/-- Left whiskering preserves vertical composition. -/
private theorem whiskerLeftComp {X Y Z : LocallyInducedBicategory C F Q}
    (f : X ⟶ Y) {g h k : Y ⟶ Z} (η : g ⟶ h) (θ : h ⟶ k) :
    whiskerLeft f (η ≫ θ) =
      whiskerLeft f η ≫ whiskerLeft f θ := sorry
/- Proof strategy: apply `ObjectProperty.hom_ext`; use the ambient
`CategoryTheory.Bicategory.whiskerLeft_comp` law. -/

/-- Whiskering on the left by an identity is controlled by the inherited left unitors. -/
private theorem idWhiskerLeft {X Y : LocallyInducedBicategory C F Q}
    {f g : X ⟶ Y} (η : f ⟶ g) :
    whiskerLeft (𝟙 X) η =
      (leftUnitor f).hom ≫ η ≫ (leftUnitor g).inv := sorry
/- Proof strategy: apply `ObjectProperty.hom_ext`; expose the ambient cells and apply
`CategoryTheory.Bicategory.id_whiskerLeft η.hom`. -/

/-- Left whiskering by a composite is controlled by the inherited associators. -/
private theorem compWhiskerLeft {W X Y Z : LocallyInducedBicategory C F Q}
    (f : W ⟶ X) (g : X ⟶ Y) {h k : Y ⟶ Z} (η : h ⟶ k) :
    whiskerLeft (f ≫ g) η =
      (associator f g h).hom ≫
        whiskerLeft f (whiskerLeft g η) ≫
          (associator f g k).inv := sorry
/- Proof strategy: apply `ObjectProperty.hom_ext`; the resulting ambient equation is
`CategoryTheory.Bicategory.comp_whiskerLeft f.obj g.obj η.hom`. -/

/-- Right whiskering preserves identity `2`-morphisms. -/
private theorem idWhiskerRight {X Y Z : LocallyInducedBicategory C F Q}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    whiskerRight (𝟙 f) g = 𝟙 (f ≫ g) := sorry
/- Proof strategy: apply `ObjectProperty.hom_ext`; use the ambient
`CategoryTheory.Bicategory.id_whiskerRight f.obj g.obj` law. -/

/-- Whiskering on the right by an identity is controlled by the inherited right unitors. -/
private theorem whiskerRightId {X Y : LocallyInducedBicategory C F Q}
    {f g : X ⟶ Y} (η : f ⟶ g) :
    whiskerRight η (𝟙 Y) =
      (rightUnitor f).hom ≫ η ≫ (rightUnitor g).inv := sorry
/- Proof strategy: apply `ObjectProperty.hom_ext`; expose the ambient cells and apply
`CategoryTheory.Bicategory.whiskerRight_id η.hom`. -/

/-- Right whiskering by a composite is controlled by the inherited associators. -/
private theorem whiskerRightComp {W X Y Z : LocallyInducedBicategory C F Q}
    {f g : W ⟶ X} (η : f ⟶ g) (h : X ⟶ Y) (k : Y ⟶ Z) :
    whiskerRight η (h ≫ k) =
      (associator f h k).inv ≫
        whiskerRight (whiskerRight η h) k ≫
          (associator g h k).hom := sorry
/- Proof strategy: apply `ObjectProperty.hom_ext`; the underlying equation is the ambient
`CategoryTheory.Bicategory.whiskerRight_comp η.hom h.obj k.obj` law. -/

/-- Right whiskering preserves vertical composition. -/
private theorem compWhiskerRight {X Y Z : LocallyInducedBicategory C F Q}
    {f g h : X ⟶ Y} (η : f ⟶ g) (θ : g ⟶ h) (k : Y ⟶ Z) :
    whiskerRight (η ≫ θ) k =
      whiskerRight η k ≫ whiskerRight θ k := sorry
/- Proof strategy: apply `ObjectProperty.hom_ext`; use the ambient
`CategoryTheory.Bicategory.comp_whiskerRight η.hom θ.hom k.obj` law. -/

/-- Left and right whiskering satisfy the inherited associativity comparison. -/
private theorem whiskerAssoc {W X Y Z : LocallyInducedBicategory C F Q}
    (f : W ⟶ X) {g h : X ⟶ Y} (η : g ⟶ h) (k : Y ⟶ Z) :
    whiskerRight (whiskerLeft f η) k =
      (associator f g k).hom ≫
        whiskerLeft f (whiskerRight η k) ≫
          (associator f h k).inv := sorry
/- Proof strategy: apply `ObjectProperty.hom_ext`; use the ambient
`CategoryTheory.Bicategory.whisker_assoc f.obj η.hom k.obj` law. -/

/-- Left and right whiskering satisfy the inherited exchange law. -/
private theorem whiskerExchange {X Y Z : LocallyInducedBicategory C F Q}
    {f g : X ⟶ Y} {h k : Y ⟶ Z} (η : f ⟶ g) (θ : h ⟶ k) :
    whiskerLeft f θ ≫ whiskerRight η k =
      whiskerRight η h ≫ whiskerLeft g θ := sorry
/- Proof strategy: apply `ObjectProperty.hom_ext`; the remaining equality is the ambient
`CategoryTheory.Bicategory.whisker_exchange η.hom θ.hom`. -/

/-- The inherited associators satisfy the pentagon equation. -/
private theorem pentagon {V W X Y Z : LocallyInducedBicategory C F Q}
    (f : V ⟶ W) (g : W ⟶ X) (h : X ⟶ Y) (k : Y ⟶ Z) :
    whiskerRight (associator f g h).hom k ≫
        (associator f (g ≫ h) k).hom ≫
          whiskerLeft f (associator g h k).hom =
      (associator (f ≫ g) h k).hom ≫
        (associator f g (h ≫ k)).hom := sorry
/- Proof strategy: apply `ObjectProperty.hom_ext`; the ambient representatives satisfy
`CategoryTheory.Bicategory.pentagon f.obj g.obj h.obj k.obj`. -/

/-- The inherited associators and unitors satisfy the triangle equation. -/
private theorem triangle {X Y Z : LocallyInducedBicategory C F Q}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (associator f (𝟙 Y) g).hom ≫
        whiskerLeft f (leftUnitor g).hom =
      whiskerRight (rightUnitor f).hom g := sorry
/- Proof strategy: apply `ObjectProperty.hom_ext`; use the ambient
`CategoryTheory.Bicategory.triangle f.obj g.obj` law. -/

end Implementation

/-- The selected `1`-morphisms and all ambient `2`-morphisms between them inherit a bicategory
structure from the ambient bicategory. -/
@[stacks 0040 "bicategory structure on selected ambient morphisms"]
instance bicategory : Bicategory (LocallyInducedBicategory C F Q) where
  homCategory X Y := inferInstanceAs (Category (Q X Y).FullSubcategory)
  whiskerLeft := Implementation.whiskerLeft
  whiskerRight := Implementation.whiskerRight
  associator := Implementation.associator
  leftUnitor := Implementation.leftUnitor
  rightUnitor := Implementation.rightUnitor
  whiskerLeft_id := Implementation.whiskerLeftId
  whiskerLeft_comp := Implementation.whiskerLeftComp
  id_whiskerLeft := Implementation.idWhiskerLeft
  comp_whiskerLeft := Implementation.compWhiskerLeft
  id_whiskerRight := Implementation.idWhiskerRight
  comp_whiskerRight := Implementation.compWhiskerRight
  whiskerRight_id := Implementation.whiskerRightId
  whiskerRight_comp := Implementation.whiskerRightComp
  whisker_assoc := Implementation.whiskerAssoc
  whisker_exchange := Implementation.whiskerExchange
  pentagon := Implementation.pentagon
  triangle := Implementation.triangle

end Construction

/-- The ambient representative of left whiskering in a locally induced bicategory is ambient
left whiskering. -/
@[simp]
lemma whiskerLeft.toAmbient {X Y Z : LocallyInducedBicategory C F Q}
    (f : X ⟶ Y) {g h : Y ⟶ Z} (η : g ⟶ h) :
    (f ◁ η).hom = f.obj ◁ η.hom := sorry
/- Proof strategy: unfold the bicategory instance and `Implementation.whiskerLeft`. -/

/-- The ambient representative of right whiskering in a locally induced bicategory is ambient
right whiskering. -/
@[simp]
lemma whiskerRight.toAmbient {X Y Z : LocallyInducedBicategory C F Q}
    {f g : X ⟶ Y} (η : f ⟶ g) (h : Y ⟶ Z) :
    (η ▷ h).hom = η.hom ▷ h.obj := sorry
/- Proof strategy: unfold the bicategory instance and `Implementation.whiskerRight`. -/

end LocallyInducedBicategory

end Bicategory

end CategoryTheory
