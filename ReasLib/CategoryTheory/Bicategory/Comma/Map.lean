/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Comma.Basic.Bicategory
public import ReasLib.CategoryTheory.Bicategory.Comma.Projection.Endpoint

@[expose] public section

/-!
# Mapping colax comma bicategories

This leaf owns postcomposition of the two-sided colax comma construction by a
pseudofunctor, together with object, map, cell, and coherence comparison computations.
-/

universe wA vA uA wB vB uB wC vC uC wD vD uD

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace Bicategory

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {B : Type uB} [Bicategory.{wB, vB} B]
variable {C : Type uC} [Bicategory.{wC, vC} C]

namespace ColaxComma

variable {F : A ⥤ᵖ C} {G : B ⥤ᵖ C}

section MapImplementation

variable {D : Type uD} [Bicategory.{wD, vD} D]

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/- Implementation boundary: applying a pseudofunctor to the structural arrow and comparison
cell is explicit below. Only compatibility and pseudofunctor coherence are proof-valued. -/

/-- Apply a pseudofunctor to the structural arrow of a colax comma object. -/
private def mapObj (H : C ⥤ᵖ D) (S : ColaxComma F G) :
    ColaxComma (F.comp H) (G.comp H) where
  left := S.left
  right := S.right
  hom := H.map S.hom

/-- Apply a pseudofunctor to a colax comma `1`-morphism, inserting its composition
comparisons on the two sides of the mapped structural cell. -/
private def mapHom (H : C ⥤ᵖ D) {S T : ColaxComma F G} (f : S ⟶ T) :
    mapObj H S ⟶ mapObj H T where
  left := f.left
  right := f.right
  cell :=
    (H.mapComp (F.map f.left) T.hom).inv ≫ H.map₂ f.cell ≫
      (H.mapComp S.hom (G.map f.right)).hom

/-- The mapped endpoint cells satisfy the compatibility equation for the mapped comma
comparison cells. -/
private theorem map₂_w (H : C ⥤ᵖ D)
    {S T : ColaxComma F G} {f g : S ⟶ T} (η : f ⟶ g) :
    ((F.comp H).map₂ η.left ▷ (mapObj H T).hom) ≫ (mapHom H g).cell =
      (mapHom H f).cell ≫
        ((mapObj H S).hom ◁ (G.comp H).map₂ η.right) := sorry
/- Proof strategy: expand `mapHom`, use `η.w`, and apply pseudofunctoriality of `H.map₂`
through the two composition comparisons. -/

/-- Apply a pseudofunctor to a colax comma `2`-morphism. The endpoint cells are unchanged
because the endpoint bicategories are unchanged. -/
private def map₂ (H : C ⥤ᵖ D)
    {S T : ColaxComma F G} {f g : S ⟶ T} (η : f ⟶ g) :
    mapHom H f ⟶ mapHom H g :=
  hom₂Mk η.left η.right (map₂_w H η)

/-- Mapping colax comma `2`-morphisms preserves identities. -/
private theorem map₂_id (H : C ⥤ᵖ D)
    {S T : ColaxComma F G} (f : S ⟶ T) :
    map₂ H (𝟙 f) = 𝟙 (mapHom H f) := sorry
/- Proof strategy: apply `Hom₂.ext`; both endpoint components are identities. -/

/-- Mapping colax comma `2`-morphisms preserves vertical composition. -/
private theorem map₂_comp (H : C ⥤ᵖ D)
    {S T : ColaxComma F G} {f g h : S ⟶ T}
    (η : f ⟶ g) (θ : g ⟶ h) :
    map₂ H (η ≫ θ) = map₂ H η ≫ map₂ H θ := sorry
/- Proof strategy: apply `Hom₂.ext`; both endpoint components preserve vertical
composition definitionally. -/

/-- The underlying prelax functor obtained by applying `H` to every comma structural arrow and
comparison cell. -/
private def mapPrelax (H : C ⥤ᵖ D) :
    PrelaxFunctor (ColaxComma F G) (ColaxComma (F.comp H) (G.comp H)) where
  obj := mapObj H
  map := mapHom H
  map₂ := map₂ H
  map₂_id := map₂_id H
  map₂_comp := map₂_comp H

/-- The left-endpoint isomorphism used in the identity comparison of comma mapping. -/
private def mapIdLeftIso (H : C ⥤ᵖ D) (S : ColaxComma F G) :
    (mapHom H (𝟙 S)).left ≅
      ((𝟙 (mapObj H S)) : mapObj H S ⟶ mapObj H S).left :=
  Iso.refl _

/-- The right-endpoint isomorphism used in the identity comparison of comma mapping. -/
private def mapIdRightIso (H : C ⥤ᵖ D) (S : ColaxComma F G) :
    (mapHom H (𝟙 S)).right ≅
      ((𝟙 (mapObj H S)) : mapObj H S ⟶ mapObj H S).right :=
  Iso.refl _

/-- Compatibility of the endpoint identity isomorphisms with the mapped comma comparison
cells. -/
private theorem mapId_w (H : C ⥤ᵖ D) (S : ColaxComma F G) :
    ((F.comp H).map₂ (mapIdLeftIso H S).hom ▷ (mapObj H S).hom) ≫
        ((𝟙 (mapObj H S)) : mapObj H S ⟶ mapObj H S).cell =
      (mapHom H (𝟙 S)).cell ≫
        ((mapObj H S).hom ◁ (G.comp H).map₂ (mapIdRightIso H S).hom) := sorry
/- Proof strategy: expand the comma identity and `mapHom`; the equation is the identity
coherence of `H` combined with naturality of its composition comparisons. -/

/-- The identity comparison for mapping a colax comma bicategory along `H`. -/
private def mapId (H : C ⥤ᵖ D) (S : ColaxComma F G) :
    (mapPrelax H).map (𝟙 S) ≅ 𝟙 ((mapPrelax H).obj S) :=
  isoMk (mapIdLeftIso H S) (mapIdRightIso H S) (mapId_w H S)

/-- The left-endpoint isomorphism used in the composition comparison of comma mapping. -/
private def mapCompLeftIso (H : C ⥤ᵖ D)
    {S T U : ColaxComma F G} (f : S ⟶ T) (g : T ⟶ U) :
    (mapHom H (f ≫ g)).left ≅ (mapHom H f ≫ mapHom H g).left :=
  Iso.refl _

/-- The right-endpoint isomorphism used in the composition comparison of comma mapping. -/
private def mapCompRightIso (H : C ⥤ᵖ D)
    {S T U : ColaxComma F G} (f : S ⟶ T) (g : T ⟶ U) :
    (mapHom H (f ≫ g)).right ≅ (mapHom H f ≫ mapHom H g).right :=
  Iso.refl _

/-- Compatibility of the endpoint composition isomorphisms with the mapped comma comparison
cells. -/
private theorem mapComp_w (H : C ⥤ᵖ D)
    {S T U : ColaxComma F G} (f : S ⟶ T) (g : T ⟶ U) :
    ((F.comp H).map₂ (mapCompLeftIso H f g).hom ▷ (mapObj H U).hom) ≫
        (mapHom H f ≫ mapHom H g).cell =
      (mapHom H (f ≫ g)).cell ≫
        ((mapObj H S).hom ◁ (G.comp H).map₂
          (mapCompRightIso H f g).hom) := sorry
/- Proof strategy: expand comma composition and `mapHom`, then use the composition coherence
of `H` and its compatibility with left and right whiskering. -/

/-- The composition comparison for mapping a colax comma bicategory along `H`. -/
private def mapComp (H : C ⥤ᵖ D)
    {S T U : ColaxComma F G} (f : S ⟶ T) (g : T ⟶ U) :
    (mapPrelax H).map (f ≫ g) ≅
      (mapPrelax H).map f ≫ (mapPrelax H).map g :=
  isoMk (mapCompLeftIso H f g) (mapCompRightIso H f g)
    (mapComp_w H f g)

/-- Mapping colax comma cells preserves left whiskering. -/
private theorem map₂_whiskerLeft (H : C ⥤ᵖ D) :
    ∀ {S T U : ColaxComma F G} (f : S ⟶ T) {g h : T ⟶ U} (η : g ⟶ h),
      (mapPrelax H).map₂ (f ◁ η) =
        (mapComp H f g).hom ≫
          (mapPrelax H).map f ◁ (mapPrelax H).map₂ η ≫
          (mapComp H f h).inv := sorry
/- Proof strategy: apply `Hom₂.ext`; both endpoint equations reduce to identity comparison
cancellation because comma mapping leaves endpoint cells unchanged. -/

/-- Mapping colax comma cells preserves right whiskering. -/
private theorem map₂_whiskerRight (H : C ⥤ᵖ D) :
    ∀ {S T U : ColaxComma F G} {f g : S ⟶ T} (η : f ⟶ g) (h : T ⟶ U),
      (mapPrelax H).map₂ (η ▷ h) =
        (mapComp H f h).hom ≫
          (mapPrelax H).map₂ η ▷ (mapPrelax H).map h ≫
          (mapComp H g h).inv := sorry
/- Proof strategy: apply `Hom₂.ext`; both endpoint equations reduce to identity comparison
cancellation because comma mapping leaves endpoint cells unchanged. -/

/-- Mapping colax comma cells preserves associators. -/
private theorem map₂_associator (H : C ⥤ᵖ D) :
    ∀ {R S T U : ColaxComma F G} (f : R ⟶ S) (g : S ⟶ T) (h : T ⟶ U),
      (mapPrelax H).map₂ (α_ f g h).hom =
        (mapComp H (f ≫ g) h).hom ≫
          (mapComp H f g).hom ▷ (mapPrelax H).map h ≫
          (α_ ((mapPrelax H).map f) ((mapPrelax H).map g)
            ((mapPrelax H).map h)).hom ≫
          (mapPrelax H).map f ◁ (mapComp H g h).inv ≫
          (mapComp H f (g ≫ h)).inv := sorry
/- Proof strategy: apply `Hom₂.ext`; the two endpoint equations are the ambient associator
coherence with identity comparison cells. -/

/-- Mapping colax comma cells preserves left unitors. -/
private theorem map₂_leftUnitor (H : C ⥤ᵖ D) :
    ∀ {S T : ColaxComma F G} (f : S ⟶ T),
      (mapPrelax H).map₂ (λ_ f).hom =
        (mapComp H (𝟙 S) f).hom ≫
          (mapId H S).hom ▷ (mapPrelax H).map f ≫
          (λ_ ((mapPrelax H).map f)).hom := sorry
/- Proof strategy: apply `Hom₂.ext`; both endpoint equations are the ambient left-unitor
coherence after trivial endpoint comparisons are removed. -/

/-- Mapping colax comma cells preserves right unitors. -/
private theorem map₂_rightUnitor (H : C ⥤ᵖ D) :
    ∀ {S T : ColaxComma F G} (f : S ⟶ T),
      (mapPrelax H).map₂ (ρ_ f).hom =
        (mapComp H f (𝟙 T)).hom ≫
          (mapPrelax H).map f ◁ (mapId H T).hom ≫
          (ρ_ ((mapPrelax H).map f)).hom := sorry
/- Proof strategy: apply `Hom₂.ext`; both endpoint equations are the ambient right-unitor
coherence after trivial endpoint comparisons are removed. -/

end Implementation

variable (F G) in
/-- Apply a pseudofunctor to the structural arrows and comparison cells of a colax comma
bicategory.

The endpoint objects, `1`-morphisms, and `2`-morphisms are unchanged. A structural arrow
`S.hom` is sent to `H.map S.hom`, while a comma comparison is surrounded by the two composition
comparisons of `H`. This is the two-sided, shape-independent owner behind transport of
costructured arrows and conical pseudocones.

The two comma legs are explicit because `H` does not determine the source
comma bicategory. -/
def map (H : C ⥤ᵖ D) :
    ColaxComma F G ⥤ᵖ ColaxComma (F.comp H) (G.comp H) where
  toPrelaxFunctor := Implementation.mapPrelax H
  mapId := Implementation.mapId H
  mapComp := Implementation.mapComp H
  map₂_whisker_left := Implementation.map₂_whiskerLeft H
  map₂_whisker_right := Implementation.map₂_whiskerRight H
  map₂_associator := Implementation.map₂_associator H
  map₂_left_unitor := Implementation.map₂_leftUnitor H
  map₂_right_unitor := Implementation.map₂_rightUnitor H

/-- Mapping a colax comma bicategory commutes strictly with its left endpoint
projection.

Both sides retain the left endpoint object, `1`-morphism, and `2`-morphism;
the comparison data are the canonical identity comparisons. -/
theorem map.fst (H : C ⥤ᵖ D) :
    (map F G H).comp (fst (F.comp H) (G.comp H)) = fst F G := sorry

/-- Mapping a colax comma bicategory commutes strictly with its right endpoint
projection.

Both sides retain the right endpoint object, `1`-morphism, and `2`-morphism;
the comparison data are the canonical identity comparisons. -/
theorem map.snd (H : C ⥤ᵖ D) :
    (map F G H).comp (snd (F.comp H) (G.comp H)) = snd F G := sorry

/-- Mapping a comma object leaves its left endpoint unchanged. -/
@[simp]
theorem map.obj.left (H : C ⥤ᵖ D) (S : ColaxComma F G) :
    ((map F G H).obj S).left = S.left := sorry
/- Proof strategy: unfold `map` and project the left field of `Implementation.mapObj`. -/

/-- Mapping a comma object leaves its right endpoint unchanged. -/
@[simp]
theorem map.obj.right (H : C ⥤ᵖ D) (S : ColaxComma F G) :
    ((map F G H).obj S).right = S.right := sorry
/- Proof strategy: unfold `map` and project the right field of `Implementation.mapObj`. -/

/-- Mapping a comma object applies `H` to its structural arrow. -/
@[simp]
theorem map.obj.hom (H : C ⥤ᵖ D) (S : ColaxComma F G) :
    ((map F G H).obj S).hom = H.map S.hom := sorry
/- Proof strategy: unfold `map` and project the structural-arrow field of
`Implementation.mapObj`. -/

/-- Mapping a comma `1`-morphism leaves its left endpoint map unchanged. -/
@[simp]
theorem map.hom.left (H : C ⥤ᵖ D)
    {S T : ColaxComma F G} (f : S ⟶ T) :
    ((map F G H).map f).left = f.left := sorry
/- Proof strategy: unfold `map` and project the left field of `Implementation.mapHom`. -/

/-- Mapping a comma `1`-morphism leaves its right endpoint map unchanged. -/
@[simp]
theorem map.hom.right (H : C ⥤ᵖ D)
    {S T : ColaxComma F G} (f : S ⟶ T) :
    ((map F G H).map f).right = f.right := sorry
/- Proof strategy: unfold `map` and project the right field of `Implementation.mapHom`. -/

/-- The structural cell of a mapped comma `1`-morphism is the mapped original cell surrounded
by the inverse source-side and forward target-side composition comparisons of `H`. -/
@[simp]
theorem map.hom.cell (H : C ⥤ᵖ D)
    {S T : ColaxComma F G} (f : S ⟶ T) :
    ((map F G H).map f).cell =
      (H.mapComp (F.map f.left) T.hom).inv ≫ H.map₂ f.cell ≫
        (H.mapComp S.hom (G.map f.right)).hom := sorry
/- Proof strategy: unfold `map` and read the explicit cell field of
`Implementation.mapHom`. -/

/-- Mapping a comma `2`-morphism leaves its left endpoint cell unchanged. -/
@[simp]
theorem map.map₂.left (H : C ⥤ᵖ D)
    {S T : ColaxComma F G} {f g : S ⟶ T} (η : f ⟶ g) :
    ((map F G H).map₂ η).left = η.left := sorry
/- Proof strategy: unfold `map` and `Implementation.map₂`, then apply `hom₂Mk`. -/

/-- Mapping a comma `2`-morphism leaves its right endpoint cell unchanged. -/
@[simp]
theorem map.map₂.right (H : C ⥤ᵖ D)
    {S T : ColaxComma F G} {f g : S ⟶ T} (η : f ⟶ g) :
    ((map F G H).map₂ η).right = η.right := sorry
/- Proof strategy: unfold `map` and `Implementation.map₂`, then apply `hom₂Mk`. -/

/-- The forward identity comparison for comma mapping is the identity cell on the left
endpoint. -/
@[simp]
theorem map.mapId.hom.left (H : C ⥤ᵖ D) (S : ColaxComma F G) :
    ((map F G H).mapId S).hom.left = 𝟙 (𝟙 S.left) := sorry
/- Proof strategy: unfold `map`, `Implementation.mapId`, and `isoMk`; its left endpoint
isomorphism is reflexivity. -/

/-- The forward identity comparison for comma mapping is the identity cell on the right
endpoint. -/
@[simp]
theorem map.mapId.hom.right (H : C ⥤ᵖ D) (S : ColaxComma F G) :
    ((map F G H).mapId S).hom.right = 𝟙 (𝟙 S.right) := sorry
/- Proof strategy: unfold `map`, `Implementation.mapId`, and `isoMk`; its right endpoint
isomorphism is reflexivity. -/

/-- The inverse identity comparison for comma mapping is the identity cell on the left
endpoint. -/
@[simp]
theorem map.mapId.inv.left (H : C ⥤ᵖ D) (S : ColaxComma F G) :
    ((map F G H).mapId S).inv.left = 𝟙 (𝟙 S.left) := sorry
/- Proof strategy: unfold `map`, `Implementation.mapId`, and `isoMk`; the inverse left
endpoint of a reflexivity isomorphism is the identity cell. -/

/-- The inverse identity comparison for comma mapping is the identity cell on the right
endpoint. -/
@[simp]
theorem map.mapId.inv.right (H : C ⥤ᵖ D) (S : ColaxComma F G) :
    ((map F G H).mapId S).inv.right = 𝟙 (𝟙 S.right) := sorry
/- Proof strategy: unfold `map`, `Implementation.mapId`, and `isoMk`; the inverse right
endpoint of a reflexivity isomorphism is the identity cell. -/

/-- The forward composition comparison for comma mapping is the identity cell on the left
endpoint. -/
@[simp]
theorem map.mapComp.hom.left (H : C ⥤ᵖ D)
    {S T U : ColaxComma F G} (f : S ⟶ T) (g : T ⟶ U) :
    ((map F G H).mapComp f g).hom.left = 𝟙 (f.left ≫ g.left) := sorry
/- Proof strategy: unfold `map`, `Implementation.mapComp`, and `isoMk`; its left endpoint
isomorphism is reflexivity. -/

/-- The forward composition comparison for comma mapping is the identity cell on the right
endpoint. -/
@[simp]
theorem map.mapComp.hom.right (H : C ⥤ᵖ D)
    {S T U : ColaxComma F G} (f : S ⟶ T) (g : T ⟶ U) :
    ((map F G H).mapComp f g).hom.right = 𝟙 (f.right ≫ g.right) := sorry
/- Proof strategy: unfold `map`, `Implementation.mapComp`, and `isoMk`; its right endpoint
isomorphism is reflexivity. -/

/-- The inverse composition comparison for comma mapping is the identity cell on the left
endpoint. -/
@[simp]
theorem map.mapComp.inv.left (H : C ⥤ᵖ D)
    {S T U : ColaxComma F G} (f : S ⟶ T) (g : T ⟶ U) :
    ((map F G H).mapComp f g).inv.left = 𝟙 (f.left ≫ g.left) := sorry
/- Proof strategy: unfold `map`, `Implementation.mapComp`, and `isoMk`; the inverse left
endpoint of a reflexivity isomorphism is the identity cell. -/

/-- The inverse composition comparison for comma mapping is the identity cell on the right
endpoint. -/
@[simp]
theorem map.mapComp.inv.right (H : C ⥤ᵖ D)
    {S T U : ColaxComma F G} (f : S ⟶ T) (g : T ⟶ U) :
    ((map F G H).mapComp f g).inv.right = 𝟙 (f.right ≫ g.right) := sorry
/- Proof strategy: unfold `map`, `Implementation.mapComp`, and `isoMk`; the inverse right
endpoint of a reflexivity isomorphism is the identity cell. -/

/- Data audit (mathlib 4.32): `ColaxComma.map` stores its mapped structural arrows, comparison
cells, endpoint `2`-cells, and both directions of its identity and composition comparison
isomorphisms explicitly. Its `sorryAx` dependencies are confined to compatibility equations and
pseudofunctor coherence fields; no endpoint, structural arrow, comparison cell, or isomorphism
component is selected by a proof witness. -/

end MapImplementation

end ColaxComma
end Bicategory
end CategoryTheory
