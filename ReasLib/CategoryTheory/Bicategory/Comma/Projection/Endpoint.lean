module

public import ReasLib.CategoryTheory.Bicategory.Comma.Basic.Computation

@[expose] public section

/-!
# Endpoint projections of colax comma bicategories

This leaf owns the two canonical endpoint pseudofunctors of a colax comma
bicategory and their computation API.
-/

universe wA vA uA wB vB uB wC vC uC

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace Bicategory

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]

namespace ColaxComma

variable {F : A ⥤ᵖ C} {G : B ⥤ᵖ C}

section ProjectionImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/- Implementation boundary: raw projection functor assembly and its coherence live here. Public
users consume fst and the semantic computation facade below. -/

/-- The underlying prelax functor of the left comma projection. -/
private def fstPrelax : PrelaxFunctor (ColaxComma F G) A where
  obj := fun S ↦ S.left
  map := fun f ↦ f.left
  map₂ := fun η ↦ η.left
  map₂_id := id₂_left
  map₂_comp := comp₂_left

/-- The identity comparison for the left comma projection. -/
private def fstMapId (S : ColaxComma F G) :
    fstPrelax.map (𝟙 S) ≅ 𝟙 S.left :=
  Iso.refl _

/-- The composition comparison for the left comma projection. -/
private def fstMapComp {S T U : ColaxComma F G} (f : S ⟶ T) (g : T ⟶ U) :
    fstPrelax.map (f ≫ g) ≅ f.left ≫ g.left :=
  Iso.refl _

/-- Left whiskering coherence for the left comma projection. -/
private theorem fstMap₂_whiskerLeft {S T U : ColaxComma F G} (f : S ⟶ T)
    {g h : T ⟶ U} (η : g ⟶ h) :
    fstPrelax.map₂ (f ◁ η) =
      (fstMapComp f g).hom ≫ f.left ◁ η.left ≫ (fstMapComp f h).inv := sorry
/- Proof strategy: unfold `fstPrelax`, `fstMapComp`, and comma left whiskering; reduce to
identity-isomorphism cancellation in the left endpoint hom-category. -/

/-- Right whiskering coherence for the left comma projection. -/
private theorem fstMap₂_whiskerRight {S T U : ColaxComma F G} {f g : S ⟶ T}
    (η : f ⟶ g) (h : T ⟶ U) :
    fstPrelax.map₂ (η ▷ h) =
      (fstMapComp f h).hom ≫ η.left ▷ h.left ≫ (fstMapComp g h).inv := sorry
/- Proof strategy: unfold the left projection and comma right whiskering; the equation reduces to
cancellation of the trivial composition comparisons. -/

/-- Associator coherence for the left comma projection. -/
private theorem fstMap₂_associator {R S T U : ColaxComma F G}
    (f : R ⟶ S) (g : S ⟶ T) (h : T ⟶ U) :
    fstPrelax.map₂ (α_ f g h).hom =
      (fstMapComp (f ≫ g) h).hom ≫ (fstMapComp f g).hom ▷ h.left ≫
        (α_ f.left g.left h.left).hom ≫ f.left ◁ (fstMapComp g h).inv ≫
          (fstMapComp f (g ≫ h)).inv := sorry
/- Proof strategy: unfold the left projection data; its image of the comma associator is the
ambient left-endpoint associator, with identity comparison cells cancelling. -/

/-- Left-unitor coherence for the left comma projection. -/
private theorem fstMap₂_leftUnitor {S T : ColaxComma F G} (f : S ⟶ T) :
    fstPrelax.map₂ (λ_ f).hom =
      (fstMapComp (𝟙 S) f).hom ≫ (fstMapId S).hom ▷ f.left ≫
        (λ_ f.left).hom := sorry
/- Proof strategy: unfold the left projection, comma left unitor, and identity comparisons; reduce
to the ambient left-unitor equation. -/

/-- Right-unitor coherence for the left comma projection. -/
private theorem fstMap₂_rightUnitor {S T : ColaxComma F G} (f : S ⟶ T) :
    fstPrelax.map₂ (ρ_ f).hom =
      (fstMapComp f (𝟙 T)).hom ≫ f.left ◁ (fstMapId T).hom ≫
        (ρ_ f.left).hom := sorry
/- Proof strategy: unfold the left projection, comma right unitor, and identity comparisons; reduce
to the ambient right-unitor equation. -/

end Implementation

variable (F G) in
/-- The canonical projection from a colax comma bicategory to its left endpoint
bicategory.

The two legs are explicit because this pseudofunctor has no value input from
which Lean can recover them. -/
def fst : ColaxComma F G ⥤ᵖ A where
  toPrelaxFunctor := Implementation.fstPrelax
  mapId := Implementation.fstMapId
  mapComp := Implementation.fstMapComp
  map₂_whisker_left := Implementation.fstMap₂_whiskerLeft
  map₂_whisker_right := Implementation.fstMap₂_whiskerRight
  map₂_associator := Implementation.fstMap₂_associator
  map₂_left_unitor := Implementation.fstMap₂_leftUnitor
  map₂_right_unitor := Implementation.fstMap₂_rightUnitor

/-- The left projection returns the left endpoint on objects. -/
@[simp]
theorem fst_obj (S : ColaxComma F G) :
    (fst F G).obj S = S.left := sorry
/- Proof strategy: unfold fst and project the object field of its private prelax core. -/

/-- The left projection returns the left component of a comma morphism. -/
@[simp]
theorem fst_map {S T : ColaxComma F G} (f : S ⟶ T) :
    (fst F G).map f = f.left := sorry
/- Proof strategy: unfold fst and project the map field of its private prelax core. -/

/-- The left projection returns the left component of a comma 2-morphism. -/
@[simp]
theorem fst_map₂ {S T : ColaxComma F G} {f g : S ⟶ T} (η : f ⟶ g) :
    (fst F G).map₂ η = η.left := sorry
/- Proof strategy: unfold fst and project the 2-morphism map of its private prelax core. -/

/-- The identity comparison of the left projection is reflexivity. -/
@[simp]
theorem fst_mapId (S : ColaxComma F G) :
    (fst F G).mapId S = Iso.refl (𝟙 S.left) := sorry
/- Proof strategy: unfold fst and read the private identity comparison. -/

/-- The composition comparison of the left projection is reflexivity. -/
@[simp]
theorem fst_mapComp {S T U : ColaxComma F G} (f : S ⟶ T) (g : T ⟶ U) :
    (fst F G).mapComp f g = Iso.refl (f.left ≫ g.left) := sorry
/- Proof strategy: unfold fst and read the private composition comparison. -/

namespace Implementation

/- Implementation boundary: raw right-projection assembly and coherence stay private; snd and its
semantic computation facade are the public surface. -/

/-- The underlying prelax functor of the right comma projection. -/
private def sndPrelax : PrelaxFunctor (ColaxComma F G) B where
  obj := fun S ↦ S.right
  map := fun f ↦ f.right
  map₂ := fun η ↦ η.right
  map₂_id := id₂_right
  map₂_comp := comp₂_right

/-- The identity comparison for the right comma projection. -/
private def sndMapId (S : ColaxComma F G) :
    sndPrelax.map (𝟙 S) ≅ 𝟙 S.right :=
  Iso.refl _

/-- The composition comparison for the right comma projection. -/
private def sndMapComp {S T U : ColaxComma F G} (f : S ⟶ T) (g : T ⟶ U) :
    sndPrelax.map (f ≫ g) ≅ f.right ≫ g.right :=
  Iso.refl _

/-- Left whiskering coherence for the right comma projection. -/
private theorem sndMap₂_whiskerLeft {S T U : ColaxComma F G} (f : S ⟶ T)
    {g h : T ⟶ U} (η : g ⟶ h) :
    sndPrelax.map₂ (f ◁ η) =
      (sndMapComp f g).hom ≫ f.right ◁ η.right ≫ (sndMapComp f h).inv := sorry
/- Proof strategy: unfold the right projection and comma left whiskering; cancel its trivial
composition comparisons in the right endpoint hom-category. -/

/-- Right whiskering coherence for the right comma projection. -/
private theorem sndMap₂_whiskerRight {S T U : ColaxComma F G} {f g : S ⟶ T}
    (η : f ⟶ g) (h : T ⟶ U) :
    sndPrelax.map₂ (η ▷ h) =
      (sndMapComp f h).hom ≫ η.right ▷ h.right ≫ (sndMapComp g h).inv := sorry
/- Proof strategy: unfold `sndPrelax`, `sndMapComp`, and comma right whiskering; reduce to
identity-isomorphism cancellation at the right endpoint. -/

/-- Associator coherence for the right comma projection. -/
private theorem sndMap₂_associator {R S T U : ColaxComma F G}
    (f : R ⟶ S) (g : S ⟶ T) (h : T ⟶ U) :
    sndPrelax.map₂ (α_ f g h).hom =
      (sndMapComp (f ≫ g) h).hom ≫ (sndMapComp f g).hom ▷ h.right ≫
        (α_ f.right g.right h.right).hom ≫ f.right ◁ (sndMapComp g h).inv ≫
          (sndMapComp f (g ≫ h)).inv := sorry
/- Proof strategy: unfold the right projection data; its image of the comma associator is the
ambient right-endpoint associator, with identity comparisons cancelling. -/

/-- Left-unitor coherence for the right comma projection. -/
private theorem sndMap₂_leftUnitor {S T : ColaxComma F G} (f : S ⟶ T) :
    sndPrelax.map₂ (λ_ f).hom =
      (sndMapComp (𝟙 S) f).hom ≫ (sndMapId S).hom ▷ f.right ≫
        (λ_ f.right).hom := sorry
/- Proof strategy: unfold the right projection, comma left unitor, and identity comparisons; reduce
to the ambient left-unitor equation. -/

/-- Right-unitor coherence for the right comma projection. -/
private theorem sndMap₂_rightUnitor {S T : ColaxComma F G} (f : S ⟶ T) :
    sndPrelax.map₂ (ρ_ f).hom =
      (sndMapComp f (𝟙 T)).hom ≫ f.right ◁ (sndMapId T).hom ≫
        (ρ_ f.right).hom := sorry
/- Proof strategy: unfold the right projection, comma right unitor, and identity comparisons;
reduce to the ambient right-unitor equation. -/

end Implementation

variable (F G) in
/-- The canonical projection from a colax comma bicategory to its right endpoint
bicategory.

The two legs are explicit because this pseudofunctor has no value input from
which Lean can recover them. -/
def snd : ColaxComma F G ⥤ᵖ B where
  toPrelaxFunctor := Implementation.sndPrelax
  mapId := Implementation.sndMapId
  mapComp := Implementation.sndMapComp
  map₂_whisker_left := Implementation.sndMap₂_whiskerLeft
  map₂_whisker_right := Implementation.sndMap₂_whiskerRight
  map₂_associator := Implementation.sndMap₂_associator
  map₂_left_unitor := Implementation.sndMap₂_leftUnitor
  map₂_right_unitor := Implementation.sndMap₂_rightUnitor

/-- The right projection returns the right endpoint on objects. -/
@[simp]
theorem snd_obj (S : ColaxComma F G) :
    (snd F G).obj S = S.right := sorry
/- Proof strategy: unfold snd and project the object field of its private prelax core. -/

/-- The right projection returns the right component of a comma morphism. -/
@[simp]
theorem snd_map {S T : ColaxComma F G} (f : S ⟶ T) :
    (snd F G).map f = f.right := sorry
/- Proof strategy: unfold snd and project the map field of its private prelax core. -/

/-- The right projection returns the right component of a comma 2-morphism. -/
@[simp]
theorem snd_map₂ {S T : ColaxComma F G} {f g : S ⟶ T} (η : f ⟶ g) :
    (snd F G).map₂ η = η.right := sorry
/- Proof strategy: unfold snd and project the 2-morphism map of its private prelax core. -/

/-- The identity comparison of the right projection is reflexivity. -/
@[simp]
theorem snd_mapId (S : ColaxComma F G) :
    (snd F G).mapId S = Iso.refl (𝟙 S.right) := sorry
/- Proof strategy: unfold snd and read the private identity comparison. -/

/-- The composition comparison of the right projection is reflexivity. -/
@[simp]
theorem snd_mapComp {S T U : ColaxComma F G} (f : S ⟶ T) (g : T ⟶ U) :
    (snd F G).mapComp f g = Iso.refl (f.right ≫ g.right) := sorry
/- Proof strategy: unfold snd and read the private composition comparison. -/

end ProjectionImplementation

end ColaxComma
end Bicategory
end CategoryTheory
