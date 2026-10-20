module

public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import Mathlib.CategoryTheory.Category.Cat.AsSmall

/-!
# Universe resizing for Cat-valued pseudofunctors

Pseudofunctorial `AsSmall` resizing on `Cat` and the induced valuewise
resizing construction for Cat-valued pseudofunctors.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Cat

universe uLift v₀ u₀

variable {C D E : Cat.{v₀, u₀}}

/-- The image of a natural transformation under `AsSmall` conjugation. -/
def asSmall.map₂ {F G : C ⟶ D} (η : F ⟶ G) :
    (asSmallFunctor.{uLift}).map F ⟶ (asSmallFunctor.{uLift}).map G :=
  (Functor.whiskerLeft AsSmall.down
    (Functor.whiskerRight η.toNatTrans AsSmall.up)).toCatHom₂

/-- `AsSmall` conjugation preserves identity natural transformations. -/
theorem asSmall.map₂.id (F : C ⟶ D) :
    asSmall.map₂.{uLift} (𝟙 F) = 𝟙 ((asSmallFunctor.{uLift}).map F) := sorry
/- Proof strategy: unfold `asSmall.map₂` and use identity preservation for left and right
whiskering of natural transformations. -/

/-- `AsSmall` conjugation preserves vertical composition. -/
theorem asSmall.map₂.comp {F G H : C ⟶ D} (η : F ⟶ G) (θ : G ⟶ H) :
    asSmall.map₂.{uLift} (η ≫ θ) =
      asSmall.map₂.{uLift} η ≫ asSmall.map₂.{uLift} θ := sorry
/- Proof strategy: unfold `asSmall.map₂` and use functoriality of natural-transformation
whiskering. -/

/-- The hom functor implementing `AsSmall` conjugation on natural transformations. -/
def asSmall.mapFunctor (C D : Cat.{v₀, u₀}) :
    (C ⟶ D) ⥤ ((asSmallFunctor.{uLift}).obj C ⟶
      (asSmallFunctor.{uLift}).obj D) where
  obj := (asSmallFunctor.{uLift}).map
  map := asSmall.map₂.{uLift}
  map_id := asSmall.map₂.id.{uLift}
  map_comp := asSmall.map₂.comp.{uLift}

section AsSmallImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The implementation-level prelax core of pseudofunctorial `AsSmall` resizing. -/
private def asSmall.prelax :
    PrelaxFunctor Cat.{v₀, u₀} Cat.{max uLift v₀ u₀, max uLift v₀ u₀} :=
  PrelaxFunctor.mkOfHomFunctors (asSmallFunctor.{uLift}).obj
    asSmall.mapFunctor.{uLift}

/-- The implementation-level identity comparison for `AsSmall` resizing. -/
private def asSmall.mapIdIso (C : Cat.{v₀, u₀}) :
    (asSmall.prelax.{uLift}).map (𝟙 C) ≅ 𝟙 ((asSmall.prelax.{uLift}).obj C) :=
  eqToIso ((asSmallFunctor.{uLift}).map_id C)

/-- The implementation-level composition comparison for `AsSmall` resizing. -/
private def asSmall.mapCompIso {C D E : Cat.{v₀, u₀}} (F : C ⟶ D) (G : D ⟶ E) :
    (asSmall.prelax.{uLift}).map (F ≫ G) ≅
      (asSmall.prelax.{uLift}).map F ≫ (asSmall.prelax.{uLift}).map G :=
  eqToIso ((asSmallFunctor.{uLift}).map_comp F G)

/-- Pseudofunctorial `AsSmall` resizing preserves left whiskering. -/
private theorem asSmall.map₂.whiskerLeft :
    ∀ {C D E : Cat.{v₀, u₀}} (F : C ⟶ D) {G H : D ⟶ E} (η : G ⟶ H),
      (asSmall.prelax.{uLift}).map₂ (F ◁ η) =
        (asSmall.mapCompIso.{uLift} F G).hom ≫
          (asSmall.prelax.{uLift}).map F ◁ (asSmall.prelax.{uLift}).map₂ η ≫
          (asSmall.mapCompIso.{uLift} F H).inv := sorry
/- Proof strategy: pass to underlying natural transformations and combine functor whiskering
with `Cat.asSmallFunctor.map_comp`. -/

/-- Pseudofunctorial `AsSmall` resizing preserves right whiskering. -/
private theorem asSmall.map₂.whiskerRight :
    ∀ {C D E : Cat.{v₀, u₀}} {F G : C ⟶ D} (η : F ⟶ G) (H : D ⟶ E),
      (asSmall.prelax.{uLift}).map₂ (η ▷ H) =
        (asSmall.mapCompIso.{uLift} F H).hom ≫
          (asSmall.prelax.{uLift}).map₂ η ▷ (asSmall.prelax.{uLift}).map H ≫
          (asSmall.mapCompIso.{uLift} G H).inv := sorry
/- Proof strategy: pass to underlying natural transformations and combine functor whiskering
with `Cat.asSmallFunctor.map_comp`. -/

/-- Pseudofunctorial `AsSmall` resizing preserves the associator. -/
private theorem asSmall.map₂.associator :
    ∀ {B C D E : Cat.{v₀, u₀}} (F : B ⟶ C) (G : C ⟶ D) (H : D ⟶ E),
      (asSmall.prelax.{uLift}).map₂ (α_ F G H).hom =
        (asSmall.mapCompIso.{uLift} (F ≫ G) H).hom ≫
          (asSmall.mapCompIso.{uLift} F G).hom ▷ (asSmall.prelax.{uLift}).map H ≫
          (α_ ((asSmall.prelax.{uLift}).map F) ((asSmall.prelax.{uLift}).map G)
            ((asSmall.prelax.{uLift}).map H)).hom ≫
          (asSmall.prelax.{uLift}).map F ◁ (asSmall.mapCompIso.{uLift} G H).inv ≫
          (asSmall.mapCompIso.{uLift} F (G ≫ H)).inv := sorry
/- Proof strategy: evaluate on an `AsSmall` object and reduce to associativity of ordinary
functor composition. -/

/-- Pseudofunctorial `AsSmall` resizing preserves the left unitor. -/
private theorem asSmall.map₂.leftUnitor :
    ∀ {C D : Cat.{v₀, u₀}} (F : C ⟶ D),
      (asSmall.prelax.{uLift}).map₂ (λ_ F).hom =
        (asSmall.mapCompIso.{uLift} (𝟙 C) F).hom ≫
          (asSmall.mapIdIso.{uLift} C).hom ▷ (asSmall.prelax.{uLift}).map F ≫
          (λ_ ((asSmall.prelax.{uLift}).map F)).hom := sorry
/- Proof strategy: evaluate on an `AsSmall` object and use identity laws for ordinary functor
composition. -/

/-- Pseudofunctorial `AsSmall` resizing preserves the right unitor. -/
private theorem asSmall.map₂.rightUnitor :
    ∀ {C D : Cat.{v₀, u₀}} (F : C ⟶ D),
      (asSmall.prelax.{uLift}).map₂ (ρ_ F).hom =
        (asSmall.mapCompIso.{uLift} F (𝟙 D)).hom ≫
          (asSmall.prelax.{uLift}).map F ◁ (asSmall.mapIdIso.{uLift} D).hom ≫
          (ρ_ ((asSmall.prelax.{uLift}).map F)).hom := sorry
/- Proof strategy: evaluate on an `AsSmall` object and use identity laws for ordinary functor
composition. -/

end Implementation

/-- Universe resizing as a pseudofunctor on `Cat`. It extends `Cat.asSmallFunctor` from
functors to natural transformations by conjugating with `AsSmall.down` and `AsSmall.up`.
Its proof-only coherence fields are private implementation details. -/
def asSmall.pseudofunctor :
    Cat.{v₀, u₀} ⥤ᵖ Cat.{max uLift v₀ u₀, max uLift v₀ u₀} where
  toPrelaxFunctor := Implementation.asSmall.prelax.{uLift}
  mapId := Implementation.asSmall.mapIdIso.{uLift}
  mapComp := Implementation.asSmall.mapCompIso.{uLift}
  map₂_whisker_left := Implementation.asSmall.map₂.whiskerLeft.{uLift}
  map₂_whisker_right := Implementation.asSmall.map₂.whiskerRight.{uLift}
  map₂_associator := Implementation.asSmall.map₂.associator.{uLift}
  map₂_left_unitor := Implementation.asSmall.map₂.leftUnitor.{uLift}
  map₂_right_unitor := Implementation.asSmall.map₂.rightUnitor.{uLift}

/-- The object action of pseudofunctorial `AsSmall` resizing. -/
@[simp]
theorem asSmall.pseudofunctor.obj (C : Cat.{v₀, u₀}) :
    asSmall.pseudofunctor.{uLift}.obj C = (asSmallFunctor.{uLift}).obj C := sorry

/-- The `1`-morphism action of pseudofunctorial `AsSmall` resizing. -/
@[simp]
theorem asSmall.pseudofunctor.map {C D : Cat.{v₀, u₀}} (F : C ⟶ D) :
    asSmall.pseudofunctor.{uLift}.map F = (asSmallFunctor.{uLift}).map F := sorry

/-- The `2`-morphism action of pseudofunctorial `AsSmall` resizing. -/
@[simp]
theorem asSmall.pseudofunctor.map₂ {C D : Cat.{v₀, u₀}}
    {F G : C ⟶ D} (η : F ⟶ G) :
    asSmall.pseudofunctor.{uLift}.map₂ η = asSmall.map₂.{uLift} η := sorry

/-- The hom-category action of pseudofunctorial `AsSmall` resizing. -/
@[simp]
theorem asSmall.pseudofunctor.mapFunctor (C D : Cat.{v₀, u₀}) :
    asSmall.pseudofunctor.{uLift}.mapFunctor C D = asSmall.mapFunctor.{uLift} C D := sorry

/-- The identity comparison of pseudofunctorial `AsSmall` resizing. -/
@[simp]
theorem asSmall.pseudofunctor.mapId (C : Cat.{v₀, u₀}) :
    asSmall.pseudofunctor.{uLift}.mapId C =
      eqToIso ((asSmallFunctor.{uLift}).map_id C) := sorry

/-- The composition comparison of pseudofunctorial `AsSmall` resizing. -/
@[simp]
theorem asSmall.pseudofunctor.mapComp {C D E : Cat.{v₀, u₀}}
    (F : C ⟶ D) (G : D ⟶ E) :
    asSmall.pseudofunctor.{uLift}.mapComp F G =
      eqToIso ((asSmallFunctor.{uLift}).map_comp F G) := sorry

end AsSmallImplementation

end Cat

namespace Pseudofunctor

universe uResize wShape vShape uShape vValue uValue

variable {J : Type uShape} [Bicategory.{wShape, vShape} J]

/-- Resize every value and component of a Cat-valued pseudofunctor into one common `AsSmall`
universe. -/
def asSmall (F : J ⥤ᵖ Cat.{vValue, uValue}) :
    J ⥤ᵖ Cat.{max uResize vValue uValue, max uResize vValue uValue} :=
  F.comp Cat.asSmall.pseudofunctor.{uResize}

/-- The object action of valuewise `AsSmall` resizing. -/
@[simp]
theorem asSmall.obj (F : J ⥤ᵖ Cat.{vValue, uValue}) (a : J) :
    (asSmall.{uResize} F).obj a =
      (Cat.asSmallFunctor.{uResize}).obj (F.obj a) := sorry

/-- The `1`-morphism action of valuewise `AsSmall` resizing. -/
@[simp]
theorem asSmall.map (F : J ⥤ᵖ Cat.{vValue, uValue})
    {a b : J} (f : a ⟶ b) :
    (asSmall.{uResize} F).map f =
      (Cat.asSmallFunctor.{uResize}).map (F.map f) := sorry

/-- The `2`-morphism action of valuewise `AsSmall` resizing. -/
@[simp]
theorem asSmall.map₂ (F : J ⥤ᵖ Cat.{vValue, uValue})
    {a b : J} {f g : a ⟶ b} (η : f ⟶ g) :
    (asSmall.{uResize} F).map₂ η =
      Cat.asSmall.map₂.{uResize} (F.map₂ η) := sorry

/-- The hom-category action of valuewise `AsSmall` resizing. -/
@[simp]
theorem asSmall.mapFunctor (F : J ⥤ᵖ Cat.{vValue, uValue}) (a b : J) :
    (asSmall.{uResize} F).mapFunctor a b =
      F.mapFunctor a b ⋙
        Cat.asSmall.mapFunctor.{uResize} (F.obj a) (F.obj b) := sorry

end Pseudofunctor

end CategoryTheory
