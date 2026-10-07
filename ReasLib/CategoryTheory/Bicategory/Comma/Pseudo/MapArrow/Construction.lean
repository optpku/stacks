module

public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo.Iso

/-!
# Mapping bicategorical arrows

Every pseudofunctor acts on the pseudo-comma bicategory of arrows: it maps
both endpoints, the structural `1`-morphism, invertibly commuting squares,
and their `2`-morphisms.  This is the bicategorical analogue of
`CategoryTheory.Functor.mapArrow`.

This leaf owns the construction.  Its public computation interface is kept
in `Comma.Pseudo.MapArrow.Computations`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe wA vA uA wB vB uB

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace Pseudofunctor

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {B : Type uB} [Bicategory.{wB, vB} B]

namespace mapArrowImplementation

/-- The mapped left endpoint projection of the pseudo-comma arrow bicategory. -/
private def leftProjection (H : A ⥤ᵖ B) :
    Pseudofunctor
      (Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)) B :=
  (Bicategory.PseudoComma.fst (Pseudofunctor.id A) (Pseudofunctor.id A)).comp H

/-- The mapped right endpoint projection of the pseudo-comma arrow bicategory. -/
private def rightProjection (H : A ⥤ᵖ B) :
    Pseudofunctor
      (Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)) B :=
  (Bicategory.PseudoComma.snd (Pseudofunctor.id A) (Pseudofunctor.id A)).comp H

/-- Apply a pseudofunctor to both endpoints and the structural arrow of a
pseudo-comma arrow object. -/
private def obj (H : A ⥤ᵖ B)
    (S : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)) :
    Bicategory.PseudoComma (Pseudofunctor.id B) (Pseudofunctor.id B) :=
  Bicategory.ColaxComma.mk
    ((leftProjection H).obj S) ((rightProjection H).obj S) (H.map S.hom)

/-- The comparison isomorphism obtained by mapping an invertibly commuting
square and inserting the composition comparisons of the pseudofunctor. -/
private noncomputable def cellIso (H : A ⥤ᵖ B)
    {S T : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    (f : S ⟶ T) :
    H.map (Bicategory.PseudoComma.left f) ≫ H.map T.hom ≅
      H.map S.hom ≫ H.map (Bicategory.PseudoComma.right f) :=
  (H.mapComp (Bicategory.PseudoComma.left f) T.hom).symm ≪≫
    H.map₂Iso (Bicategory.PseudoComma.cellIso f) ≪≫
      H.mapComp S.hom (Bicategory.PseudoComma.right f)

/-- Apply a pseudofunctor to an invertibly commuting square. -/
private noncomputable def map (H : A ⥤ᵖ B)
    {S T : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    (f : S ⟶ T) : obj H S ⟶ obj H T :=
  Bicategory.PseudoComma.homMk
    ((leftProjection H).map f) ((rightProjection H).map f) (cellIso H f)

/-- The mapped endpoint cells satisfy the pseudo-comma compatibility equation. -/
private theorem map₂_w (H : A ⥤ᵖ B)
    {S T : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    {f g : S ⟶ T} (η : f ⟶ g) :
    ((Pseudofunctor.id B).map₂ ((leftProjection H).map₂ η) ▷ (obj H T).hom) ≫
        Bicategory.PseudoComma.cell (map H g) =
      Bicategory.PseudoComma.cell (map H f) ≫
        ((obj H S).hom ◁
          (Pseudofunctor.id B).map₂ ((rightProjection H).map₂ η)) := sorry

/-- Apply a pseudofunctor to a `2`-morphism of invertibly commuting squares. -/
private noncomputable def map₂ (H : A ⥤ᵖ B)
    {S T : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    {f g : S ⟶ T} (η : f ⟶ g) : map H f ⟶ map H g :=
  Bicategory.PseudoComma.hom₂Mk
    ((leftProjection H).map₂ η) ((rightProjection H).map₂ η) (map₂_w H η)

/-- Mapping arrows preserves identity `2`-morphisms. -/
private theorem map₂_id (H : A ⥤ᵖ B)
    {S T : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    (f : S ⟶ T) : map₂ H (𝟙 f) = 𝟙 (map H f) := sorry

/-- Mapping arrows preserves vertical composition of `2`-morphisms. -/
private theorem map₂_comp (H : A ⥤ᵖ B)
    {S T : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    {f g h : S ⟶ T} (η : f ⟶ g) (θ : g ⟶ h) :
    map₂ H (η ≫ θ) = map₂ H η ≫ map₂ H θ := sorry

/-- The prelax core of componentwise mapping on pseudo-comma arrows. -/
private noncomputable def prelax (H : A ⥤ᵖ B) :
    PrelaxFunctor
      (Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A))
      (Bicategory.PseudoComma (Pseudofunctor.id B) (Pseudofunctor.id B)) where
  obj := obj H
  map := map H
  map₂ := map₂ H
  map₂_id := map₂_id H
  map₂_comp := map₂_comp H

/-- Compatibility of the mapped endpoint identity comparisons with the
mapped structural arrow. -/
private theorem mapId_w (H : A ⥤ᵖ B)
    (S : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)) :
    (((Pseudofunctor.id B).map₂ ((leftProjection H).mapId S).hom ▷
        (obj H S).hom) ≫ Bicategory.PseudoComma.cell (𝟙 (obj H S))) =
      Bicategory.PseudoComma.cell (map H (𝟙 S)) ≫
        ((obj H S).hom ◁
          (Pseudofunctor.id B).map₂ ((rightProjection H).mapId S).hom) := sorry

/-- The identity comparison for componentwise mapping on pseudo-comma arrows. -/
private noncomputable def mapId (H : A ⥤ᵖ B)
    (S : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)) :
    map H (𝟙 S) ≅ 𝟙 (obj H S) :=
  Bicategory.PseudoComma.isoMk
    ((leftProjection H).mapId S) ((rightProjection H).mapId S) (mapId_w H S)

/-- Compatibility of the mapped endpoint composition comparisons with the
mapped structural arrow. -/
private theorem mapComp_w (H : A ⥤ᵖ B)
    {S T U : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    (f : S ⟶ T) (g : T ⟶ U) :
    (((Pseudofunctor.id B).map₂ ((leftProjection H).mapComp f g).hom ▷
        (obj H U).hom) ≫ Bicategory.PseudoComma.cell (map H f ≫ map H g)) =
      Bicategory.PseudoComma.cell (map H (f ≫ g)) ≫
        ((obj H S).hom ◁
          (Pseudofunctor.id B).map₂ ((rightProjection H).mapComp f g).hom) := sorry

/-- The composition comparison for componentwise mapping on pseudo-comma arrows. -/
private noncomputable def mapComp (H : A ⥤ᵖ B)
    {S T U : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    (f : S ⟶ T) (g : T ⟶ U) :
    map H (f ≫ g) ≅ map H f ≫ map H g :=
  Bicategory.PseudoComma.isoMk
    ((leftProjection H).mapComp f g) ((rightProjection H).mapComp f g)
      (mapComp_w H f g)

/-- Mapping arrows preserves left whiskering through its composition comparisons. -/
private theorem map₂_whiskerLeft (H : A ⥤ᵖ B) :
    ∀ {S T U : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
      (f : S ⟶ T) {g h : T ⟶ U} (η : g ⟶ h),
      (prelax H).map₂ (f ◁ η) =
        (mapComp H f g).hom ≫ (prelax H).map f ◁ (prelax H).map₂ η ≫
          (mapComp H f h).inv := sorry

/-- Mapping arrows preserves right whiskering through its composition comparisons. -/
private theorem map₂_whiskerRight (H : A ⥤ᵖ B) :
    ∀ {S T U : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
      {f g : S ⟶ T} (η : f ⟶ g) (h : T ⟶ U),
      (prelax H).map₂ (η ▷ h) =
        (mapComp H f h).hom ≫ (prelax H).map₂ η ▷ (prelax H).map h ≫
          (mapComp H g h).inv := sorry

/-- Mapping arrows preserves associators through its composition comparisons. -/
private theorem map₂_associator (H : A ⥤ᵖ B) :
    ∀ {R S T U : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
      (f : R ⟶ S) (g : S ⟶ T) (h : T ⟶ U),
      (prelax H).map₂ (α_ f g h).hom =
        (mapComp H (f ≫ g) h).hom ≫
          (mapComp H f g).hom ▷ (prelax H).map h ≫
          (α_ ((prelax H).map f) ((prelax H).map g) ((prelax H).map h)).hom ≫
          (prelax H).map f ◁ (mapComp H g h).inv ≫
          (mapComp H f (g ≫ h)).inv := sorry

/-- Mapping arrows preserves left unitors through its comparisons. -/
private theorem map₂_leftUnitor (H : A ⥤ᵖ B) :
    ∀ {S T : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
      (f : S ⟶ T),
      (prelax H).map₂ (λ_ f).hom =
        (mapComp H (𝟙 S) f).hom ≫
          (mapId H S).hom ▷ (prelax H).map f ≫
          (λ_ ((prelax H).map f)).hom := sorry

/-- Mapping arrows preserves right unitors through its comparisons. -/
private theorem map₂_rightUnitor (H : A ⥤ᵖ B) :
    ∀ {S T : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
      (f : S ⟶ T),
      (prelax H).map₂ (ρ_ f).hom =
        (mapComp H f (𝟙 T)).hom ≫
          (prelax H).map f ◁ (mapId H T).hom ≫
          (ρ_ ((prelax H).map f)).hom := sorry

end mapArrowImplementation

/-- A pseudofunctor induces a pseudofunctor between its pseudo-comma arrow
bicategories.

It applies `H` to both endpoints, the structural `1`-morphism, both sides of
an invertibly commuting square, and both endpoint `2`-cells.  Its identity
and composition comparisons are induced by those of `H`. -/
noncomputable def mapArrow (H : A ⥤ᵖ B) :
    Pseudofunctor
      (Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A))
      (Bicategory.PseudoComma (Pseudofunctor.id B) (Pseudofunctor.id B)) where
  toPrelaxFunctor := mapArrowImplementation.prelax H
  mapId := mapArrowImplementation.mapId H
  mapComp := mapArrowImplementation.mapComp H
  map₂_whisker_left := mapArrowImplementation.map₂_whiskerLeft H
  map₂_whisker_right := mapArrowImplementation.map₂_whiskerRight H
  map₂_associator := mapArrowImplementation.map₂_associator H
  map₂_left_unitor := mapArrowImplementation.map₂_leftUnitor H
  map₂_right_unitor := mapArrowImplementation.map₂_rightUnitor H

/- Data audit: every non-`Prop` field of `mapArrow` is obtained explicitly
from `H`, `PseudoComma.homMk`, and `PseudoComma.isoMk`.  Deferred statements
are compatibility, functoriality, and bicategorical coherence propositions. -/

end Pseudofunctor

end CategoryTheory
