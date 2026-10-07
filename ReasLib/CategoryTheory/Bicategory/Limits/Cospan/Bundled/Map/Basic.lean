module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Bundled.Modification
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Map.Coherence.Construction
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Map.Modification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Mapping bundled bicategorical cospans

Every pseudofunctor between bicategories acts componentwise on bundled cospans. The object,
`1`-morphism, and `2`-morphism actions reuse the canonical walking-cospan map APIs; identity
and composition comparisons reuse their canonical cospan-transform isomorphisms.

This file owns the resulting pseudofunctor. Its downstream computation API is layered in
`Cospan.Bundled.Map`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w v u w' v' u'

namespace CategoryTheory.Bicategory.Cospan

variable {B : Type u} [Bicategory.{w, v} B]
variable {B' : Type u'} [Bicategory.{w', v'} B']

namespace Implementation

/-- The explicit object action of an ambient pseudofunctor on bundled cospans. -/
private def mapObj (P : B ⥤ᵖ B') (S : Cospan B) : Cospan B' where
  left := P.obj S.left
  right := P.obj S.right
  base := P.obj S.base
  fst := P.map S.fst
  snd := P.map S.snd

/-- The explicit `1`-morphism action on bundled cospans. -/
private def mapHom (P : B ⥤ᵖ B') {S T : Cospan B} (ψ : S ⟶ T) :
    mapObj P S ⟶ mapObj P T :=
  Hom.ofCospanTransform
    (CospanTransform.map (Hom.toCospanTransform ψ) P)

/-- The explicit `2`-morphism action on bundled cospans. -/
private def map₂ (P : B ⥤ᵖ B') {S T : Cospan B} {ψ φ : S ⟶ T}
    (Γ : ψ ⟶ φ) : mapHom P ψ ⟶ mapHom P φ :=
  Hom₂.ofModification
    (CospanTransform.Hom.map (Hom₂.toModification Γ) P)

/-- Componentwise mapping of cospan modifications preserves identity `2`-morphisms. -/
private theorem map₂_id (P : B ⥤ᵖ B') {S T : Cospan B} (ψ : S ⟶ T) :
    map₂ P (𝟙 ψ) = 𝟙 (mapHom P ψ) := sorry

/-- Componentwise mapping of cospan modifications preserves vertical composition. -/
private theorem map₂_comp (P : B ⥤ᵖ B') {S T : Cospan B}
    {ψ φ χ : S ⟶ T} (Γ : ψ ⟶ φ) (Δ : φ ⟶ χ) :
    map₂ P (Γ ≫ Δ) = map₂ P Γ ≫ map₂ P Δ := sorry

/-- The prelax core of componentwise mapping of bundled cospans. -/
private def mapPrelax (P : B ⥤ᵖ B') :
    PrelaxFunctor (Cospan B) (Cospan B') where
  obj := mapObj P
  map := mapHom P
  map₂ := map₂ P
  map₂_id := map₂_id P
  map₂_comp := map₂_comp P

/-- The identity comparison for componentwise mapping of bundled cospans. -/
private def mapId (P : B ⥤ᵖ B') (S : Cospan B) :
    (mapPrelax P).map (𝟙 S) ≅ 𝟙 ((mapPrelax P).obj S) :=
  InducedBicategory.isoMk
    (CospanTransform.map.idIso S.fst S.snd P)

/-- The composition comparison for componentwise mapping of bundled cospans. -/
private def mapComp (P : B ⥤ᵖ B') {R S T : Cospan B}
    (ψ : R ⟶ S) (φ : S ⟶ T) :
    (mapPrelax P).map (ψ ≫ φ) ≅
      (mapPrelax P).map ψ ≫ (mapPrelax P).map φ :=
  InducedBicategory.isoMk
    (CospanTransform.map.compIso
      (Hom.toCospanTransform ψ) (Hom.toCospanTransform φ) P)

/-- Componentwise mapping preserves left whiskering up to its composition comparisons. -/
private theorem map₂_whisker_left (P : B ⥤ᵖ B') {R S T : Cospan B}
    (ψ : R ⟶ S) {φ χ : S ⟶ T} (Γ : φ ⟶ χ) :
    (mapPrelax P).map₂ (ψ ◁ Γ) =
      (mapComp P ψ φ).hom ≫
        (mapPrelax P).map ψ ◁ (mapPrelax P).map₂ Γ ≫
          (mapComp P ψ χ).inv := sorry

/-- Componentwise mapping preserves right whiskering up to its composition comparisons. -/
private theorem map₂_whisker_right (P : B ⥤ᵖ B') {R S T : Cospan B}
    {ψ φ : R ⟶ S} (Γ : ψ ⟶ φ) (χ : S ⟶ T) :
    (mapPrelax P).map₂ (Γ ▷ χ) =
      (mapComp P ψ χ).hom ≫
        (mapPrelax P).map₂ Γ ▷ (mapPrelax P).map χ ≫
          (mapComp P φ χ).inv := sorry

/-- Componentwise mapping carries associators to associators with the standard composition
comparisons. -/
private theorem map₂_associator (P : B ⥤ᵖ B')
    {Q R S T : Cospan B} (ψ : Q ⟶ R) (φ : R ⟶ S) (χ : S ⟶ T) :
    (mapPrelax P).map₂ (α_ ψ φ χ).hom =
      (mapComp P (ψ ≫ φ) χ).hom ≫
        (mapComp P ψ φ).hom ▷ (mapPrelax P).map χ ≫
          (α_ ((mapPrelax P).map ψ) ((mapPrelax P).map φ)
            ((mapPrelax P).map χ)).hom ≫
            (mapPrelax P).map ψ ◁ (mapComp P φ χ).inv ≫
              (mapComp P ψ (φ ≫ χ)).inv := sorry

/-- Componentwise mapping carries left unitors to left unitors with the standard identity and
composition comparisons. -/
private theorem map₂_left_unitor (P : B ⥤ᵖ B') {S T : Cospan B}
    (ψ : S ⟶ T) :
    (mapPrelax P).map₂ (λ_ ψ).hom =
      (mapComp P (𝟙 S) ψ).hom ≫
        (mapId P S).hom ▷ (mapPrelax P).map ψ ≫
          (λ_ ((mapPrelax P).map ψ)).hom := sorry

/-- Componentwise mapping carries right unitors to right unitors with the standard identity
and composition comparisons. -/
private theorem map₂_right_unitor (P : B ⥤ᵖ B') {S T : Cospan B}
    (ψ : S ⟶ T) :
    (mapPrelax P).map₂ (ρ_ ψ).hom =
      (mapComp P ψ (𝟙 T)).hom ≫
        (mapPrelax P).map ψ ◁ (mapId P T).hom ≫
          (ρ_ ((mapPrelax P).map ψ)).hom := sorry

end Implementation

/-- Apply a pseudofunctor componentwise to bundled cospans and their `1`- and `2`-morphisms.

The identity and composition comparisons are respectively `CospanTransform.map.idIso` and
`CospanTransform.map.compIso`; no parallel cospan coherence data are introduced. -/
@[stacks 0040 "componentwise pseudofunctor on bundled bicategorical cospans"]
def map (P : B ⥤ᵖ B') : Cospan B ⥤ᵖ Cospan B' where
  toPrelaxFunctor := Implementation.mapPrelax P
  mapId := Implementation.mapId P
  mapComp := Implementation.mapComp P
  map₂_whisker_left := Implementation.map₂_whisker_left P
  map₂_whisker_right := Implementation.map₂_whisker_right P
  map₂_associator := Implementation.map₂_associator P
  map₂_left_unitor := Implementation.map₂_left_unitor P
  map₂_right_unitor := Implementation.map₂_right_unitor P

/- Data and axiom audit (mathlib 4.32):

Every non-`Prop` field of `map` is explicit: objects and legs use `P.obj`/`P.map`,
`1`- and `2`-morphisms use the canonical cospan transformation/modification maps, and the
comparison isomorphisms use `CospanTransform.map.idIso`/`CospanTransform.map.compIso`.
`#print axioms` reports
`[propext, sorryAx, Classical.choice, Quot.sound]`; `sorryAx` is confined to the
pseudofunctor law fields and inherited coherence. -/

end CategoryTheory.Bicategory.Cospan
