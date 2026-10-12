/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Lift
public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.Iso
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso

/-!
# Computations for locally induced bicategories

This leaf exposes the object, `1`-morphism, and `2`-morphism actions of the
canonical inclusions and strict lifts.  It lets downstream constructions read
through these strict pseudofunctors without unfolding their coherence data.
-/

@[expose] public section

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

universe w v u u' w' v' u''

namespace Bicategory

variable {B : Type u'}

namespace LocallyInducedBicategory

variable {C : Type u} [Bicategory.{w, v} C] {F : B → C}
  {Q : HomProperty F} [Q.IsMultiplicative]

section Inclusion

/-- The ambient representative of the image of a selected `1`-morphism under
the canonical inclusion is the original ambient morphism. -/
@[simp]
theorem ι.map.toAmbient {X Y : LocallyInducedBicategory C F Q} (f : X ⟶ Y) :
    ((ι C F Q).map f).hom = f.obj := sorry

/-- The ambient representative of the image of a selected `2`-morphism under
the canonical inclusion is the original ambient cell. -/
@[simp]
theorem ι.map₂.toAmbient {X Y : LocallyInducedBicategory C F Q}
    {f g : X ⟶ Y} (η : f ⟶ g) :
    ((ι C F Q).map₂ η).hom = η.hom := sorry

end Inclusion

section Lift

variable {A : Type u''} [Bicategory.{w', v'} A]

/-- The ambient representative of the image of a `1`-morphism under a strict
lift is its original ambient image. -/
@[simp]
theorem lift.map.toAmbient (G : StrictPseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    {X Y : A} (f : X ⟶ Y) :
    ((lift G map_mem).map f).obj = (G.map f).hom := sorry

/-- The ambient representative of the image of a `2`-morphism under a strict
lift is its original ambient cell. -/
@[simp]
theorem lift.map₂.toAmbient (G : StrictPseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    {X Y : A} {f g : X ⟶ Y} (η : f ⟶ g) :
    ((lift G map_mem).map₂ η).hom = (G.map₂ η).hom := sorry

/-- The ambient forward identity comparison of a strict lift is the corresponding comparison of
the original strict pseudofunctor. -/
@[simp]
theorem lift.mapId.hom.toAmbient
    (G : StrictPseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    (X : A) :
    (LocallyInducedBicategory.Iso.toAmbient
      ((lift G map_mem).mapId X)).hom =
      (InducedBicategory.Iso.toAmbient (G.mapId X)).hom := sorry

/-- The ambient inverse identity comparison of a strict lift is the corresponding comparison of
the original strict pseudofunctor. -/
@[simp]
theorem lift.mapId.inv.toAmbient
    (G : StrictPseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    (X : A) :
    (LocallyInducedBicategory.Iso.toAmbient
      ((lift G map_mem).mapId X)).inv =
      (InducedBicategory.Iso.toAmbient (G.mapId X)).inv := sorry

/-- The ambient forward composition comparison of a strict lift is the corresponding comparison
of the original strict pseudofunctor. -/
@[simp]
theorem lift.mapComp.hom.toAmbient
    (G : StrictPseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (LocallyInducedBicategory.Iso.toAmbient
      ((lift G map_mem).mapComp f g)).hom =
      (InducedBicategory.Iso.toAmbient (G.mapComp f g)).hom := sorry

/-- The ambient inverse composition comparison of a strict lift is the corresponding comparison
of the original strict pseudofunctor. -/
@[simp]
theorem lift.mapComp.inv.toAmbient
    (G : StrictPseudofunctor A (InducedBicategory C F))
    (map_mem : ∀ {X Y : A} (f : X ⟶ Y),
      Q (G.obj X) (G.obj Y) (G.map f).hom)
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (LocallyInducedBicategory.Iso.toAmbient
      ((lift G map_mem).mapComp f g)).inv =
      (InducedBicategory.Iso.toAmbient (G.mapComp f g)).inv := sorry

end Lift

section PropertyInclusion

variable {R : HomProperty F} [R.IsMultiplicative]

/-- An inclusion induced by `Q ≤ R` retains the underlying ambient
`1`-morphism. -/
@[simp]
theorem ιOfLE.map.toAmbient
    (h : Q ≤ R) {X Y : LocallyInducedBicategory C F Q} (f : X ⟶ Y) :
    ((ιOfLE h).map f).obj = f.obj := sorry

/-- An inclusion induced by `Q ≤ R` retains every ambient `2`-morphism. -/
@[simp]
theorem ιOfLE.map₂.toAmbient
    (h : Q ≤ R) {X Y : LocallyInducedBicategory C F Q}
    {f g : X ⟶ Y} (η : f ⟶ g) :
    ((ιOfLE h).map₂ η).hom = η.hom := sorry

end PropertyInclusion

section Forget

/-- The forward identity comparison of ambient forgetting is the ambient identity `2`-morphism. -/
@[simp]
theorem forget.mapId.hom (X : LocallyInducedBicategory C F Q) :
    ((forget C F Q).mapId X).hom = 𝟙 (𝟙 (F X)) := sorry

/-- The inverse identity comparison of ambient forgetting is the ambient identity `2`-morphism. -/
@[simp]
theorem forget.mapId.inv (X : LocallyInducedBicategory C F Q) :
    ((forget C F Q).mapId X).inv = 𝟙 (𝟙 (F X)) := sorry

/-- The forward composition comparison of ambient forgetting is the ambient identity `2`-morphism. -/
@[simp]
theorem forget.mapComp.hom {X Y Z : LocallyInducedBicategory C F Q}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((forget C F Q).mapComp f g).hom = 𝟙 (f.obj ≫ g.obj) := sorry

/-- The inverse composition comparison of ambient forgetting is the ambient identity `2`-morphism. -/
@[simp]
theorem forget.mapComp.inv {X Y Z : LocallyInducedBicategory C F Q}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((forget C F Q).mapComp f g).inv = 𝟙 (f.obj ≫ g.obj) := sorry

/-- Mapping a selected `2`-isomorphism along ambient forgetting retains its forward ambient cell. -/
@[simp]
theorem forget.map₂Iso.hom {X Y : LocallyInducedBicategory C F Q}
    {f g : X ⟶ Y} (η : f ≅ g) :
    ((forget C F Q).toPseudofunctor.map₂Iso η).hom =
      (LocallyInducedBicategory.Iso.toAmbient η).hom := sorry

/-- Mapping a selected `2`-isomorphism along ambient forgetting retains its inverse ambient cell. -/
@[simp]
theorem forget.map₂Iso.inv {X Y : LocallyInducedBicategory C F Q}
    {f g : X ⟶ Y} (η : f ≅ g) :
    ((forget C F Q).toPseudofunctor.map₂Iso η).inv =
      (LocallyInducedBicategory.Iso.toAmbient η).inv := sorry

end Forget

end LocallyInducedBicategory

end Bicategory

end CategoryTheory
