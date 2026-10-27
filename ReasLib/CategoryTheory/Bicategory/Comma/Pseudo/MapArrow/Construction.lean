/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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

/-- Naturality of the pasted image of a square, in the ambient hom-categories. -/
private theorem mapCell_naturality (H : A ⥤ᵖ B)
    {a b c d : A} {s : a ⟶ b} {t : c ⟶ d}
    {l l' : a ⟶ c} {r r' : b ⟶ d}
    {p : l ≫ t ⟶ s ≫ r} {q : l' ≫ t ⟶ s ≫ r'}
    (η : l ⟶ l') (θ : r ⟶ r')
    (w : (η ▷ t) ≫ q = p ≫ (s ◁ θ)) :
    (H.map₂ η ▷ H.map t) ≫
        ((H.mapComp l' t).inv ≫ H.map₂ q ≫ (H.mapComp s r').hom) =
      ((H.mapComp l t).inv ≫ H.map₂ p ≫ (H.mapComp s r).hom) ≫
        (H.map s ◁ H.map₂ θ) := by
  have hleft : (H.mapComp l t).inv ≫ H.map₂ (η ▷ t) =
      (H.map₂ η ▷ H.map t) ≫ (H.mapComp l' t).inv :=
    H.toLax.mapComp_naturality_left η t
  have hright : H.map₂ (s ◁ θ) ≫ (H.mapComp s r').hom =
      (H.mapComp s r).hom ≫ (H.map s ◁ H.map₂ θ) :=
    H.toOplax.mapComp_naturality_right s θ
  simp only [← Category.assoc]
  rw [← hleft]
  simp only [Category.assoc]
  rw [← hright]
  simpa only [H.map₂_comp, Category.assoc] using
    congrArg (fun c ↦ (H.mapComp l t).inv ≫ H.map₂ c ≫
      (H.mapComp s r').hom) w

/-- The mapped endpoint cells satisfy the pseudo-comma compatibility equation. -/
private theorem map₂_w (H : A ⥤ᵖ B)
    {S T : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    {f g : S ⟶ T} (η : f ⟶ g) :
    ((Pseudofunctor.id B).map₂ ((leftProjection H).map₂ η) ▷ (obj H T).hom) ≫
        Bicategory.PseudoComma.cell (map H g) =
      Bicategory.PseudoComma.cell (map H f) ≫
        ((obj H S).hom ◁
          (Pseudofunctor.id B).map₂ ((rightProjection H).map₂ η)) := by
  exact mapCell_naturality H η.hom.left η.hom.right η.hom.w

/-- Apply a pseudofunctor to a `2`-morphism of invertibly commuting squares. -/
private noncomputable def map₂ (H : A ⥤ᵖ B)
    {S T : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    {f g : S ⟶ T} (η : f ⟶ g) : map H f ⟶ map H g :=
  Bicategory.PseudoComma.hom₂Mk
    ((leftProjection H).map₂ η) ((rightProjection H).map₂ η) (map₂_w H η)

/-- Mapping arrows preserves identity `2`-morphisms. -/
private theorem map₂_id (H : A ⥤ᵖ B)
    {S T : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    (f : S ⟶ T) : map₂ H (𝟙 f) = 𝟙 (map H f) := by
  apply ObjectProperty.hom_ext
  exact ColaxComma.Hom₂.ext (H.map₂_id f.obj.left) (H.map₂_id f.obj.right)

/-- Mapping arrows preserves vertical composition of `2`-morphisms. -/
private theorem map₂_comp (H : A ⥤ᵖ B)
    {S T : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    {f g h : S ⟶ T} (η : f ⟶ g) (θ : g ⟶ h) :
    map₂ H (η ≫ θ) = map₂ H η ≫ map₂ H θ := by
  apply ObjectProperty.hom_ext
  exact ColaxComma.Hom₂.ext (H.map₂_comp η.hom.left θ.hom.left)
    (H.map₂_comp η.hom.right θ.hom.right)

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

/-- A pseudofunctor preserves the unitor pasting of an identity square. -/
private theorem mapCell_unit (H : A ⥤ᵖ B) {a b : A} (s : a ⟶ b) :
    ((H.mapId a).hom ▷ H.map s) ≫
        ((λ_ (H.map s)).hom ≫ (ρ_ (H.map s)).inv) =
      ((H.mapComp (𝟙 a) s).inv ≫ H.map₂ ((λ_ s).hom ≫ (ρ_ s).inv) ≫
        (H.mapComp s (𝟙 b)).hom) ≫ (H.map s ◁ (H.mapId b).hom) := by
  simp only [H.mapComp_id_left_inv, H.mapComp_id_right_hom, H.map₂_comp,
    Category.assoc, H.map₂_inv_hom_assoc, Bicategory.whiskerLeft_inv_hom, Category.comp_id]

/-- Compatibility of the mapped endpoint identity comparisons with the
mapped structural arrow. -/
private theorem mapId_w (H : A ⥤ᵖ B)
    (S : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)) :
    (((Pseudofunctor.id B).map₂ ((leftProjection H).mapId S).hom ▷
        (obj H S).hom) ≫ Bicategory.PseudoComma.cell (𝟙 (obj H S))) =
      Bicategory.PseudoComma.cell (map H (𝟙 S)) ≫
        ((obj H S).hom ◁
          (Pseudofunctor.id B).map₂ ((rightProjection H).mapId S).hom) := by
  let a : A := ColaxComma.left S
  let b : A := ColaxComma.right S
  let s : a ⟶ b := S.hom
  change ((H.map₂ ((𝟙 (𝟙 a) ≫ 𝟙 _) ≫ 𝟙 _) ≫ (H.mapId a).hom) ▷ H.map s) ≫
      ((𝟙 (𝟙 (H.obj a)) ▷ H.map s) ≫ (λ_ (H.map s)).hom ≫
        (ρ_ (H.map s)).inv ≫ (H.map s ◁ 𝟙 (𝟙 (H.obj b)))) =
    ((H.mapComp (𝟙 a) s).inv ≫
        H.map₂ ((𝟙 (𝟙 a) ▷ s) ≫ (λ_ s).hom ≫ (ρ_ s).inv ≫ (s ◁ 𝟙 (𝟙 b))) ≫
        (H.mapComp s (𝟙 b)).hom) ≫
      (H.map s ◁ (H.map₂ ((𝟙 (𝟙 b) ≫ 𝟙 _) ≫ 𝟙 _) ≫ (H.mapId b).hom))
  simpa only [Category.id_comp, Category.comp_id, H.map₂_id,
    Bicategory.id_whiskerRight, Bicategory.whiskerLeft_id] using mapCell_unit H s

/-- The identity comparison for componentwise mapping on pseudo-comma arrows. -/
private noncomputable def mapId (H : A ⥤ᵖ B)
    (S : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)) :
    map H (𝟙 S) ≅ 𝟙 (obj H S) :=
  Bicategory.PseudoComma.isoMk
    ((leftProjection H).mapId S) ((rightProjection H).mapId S) (mapId_w H S)

/-- A pseudofunctor preserves the associator pasting of two squares. -/
private theorem mapCell_comp (H : A ⥤ᵖ B) {a₁ a₂ a₃ b₁ b₂ b₃ : A}
    (s : a₁ ⟶ b₁) (t : a₂ ⟶ b₂) (u : a₃ ⟶ b₃)
    (l : a₁ ⟶ a₂) (m : a₂ ⟶ a₃) (r : b₁ ⟶ b₂) (n : b₂ ⟶ b₃)
    (p : l ≫ t ⟶ s ≫ r) (q : m ≫ u ⟶ t ≫ n) :
    ((H.mapComp l m).hom ▷ H.map u) ≫
      (α_ (H.map l) (H.map m) (H.map u)).hom ≫
      H.map l ◁ ((H.mapComp m u).inv ≫ H.map₂ q ≫ (H.mapComp t n).hom) ≫
      (α_ (H.map l) (H.map t) (H.map n)).inv ≫
      ((H.mapComp l t).inv ≫ H.map₂ p ≫ (H.mapComp s r).hom) ▷ H.map n ≫
      (α_ (H.map s) (H.map r) (H.map n)).hom =
    ((H.mapComp (l ≫ m) u).inv ≫
      H.map₂ ((α_ l m u).hom ≫ l ◁ q ≫ (α_ l t n).inv ≫ p ▷ n ≫ (α_ s r n).hom) ≫
      (H.mapComp s (r ≫ n)).hom) ≫ (H.map s ◁ (H.mapComp r n).hom) := by
  simp [H.map₂_iso_inv, H.map₂_associator, Bicategory.comp_whiskerRight,
    Bicategory.whiskerLeft_comp, Category.assoc]

/-- Compatibility of the mapped endpoint composition comparisons with the
mapped structural arrow. -/
private theorem mapComp_w (H : A ⥤ᵖ B)
    {S T U : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
    (f : S ⟶ T) (g : T ⟶ U) :
    (((Pseudofunctor.id B).map₂ ((leftProjection H).mapComp f g).hom ▷
        (obj H U).hom) ≫ Bicategory.PseudoComma.cell (map H f ≫ map H g)) =
      Bicategory.PseudoComma.cell (map H (f ≫ g)) ≫
        ((obj H S).hom ◁
          (Pseudofunctor.id B).map₂ ((rightProjection H).mapComp f g).hom) := by
  let a₁ : A := ColaxComma.left S
  let a₂ : A := ColaxComma.left T
  let a₃ : A := ColaxComma.left U
  let b₁ : A := ColaxComma.right S
  let b₂ : A := ColaxComma.right T
  let b₃ : A := ColaxComma.right U
  let s : a₁ ⟶ b₁ := S.hom
  let t : a₂ ⟶ b₂ := T.hom
  let u : a₃ ⟶ b₃ := U.hom
  let l : a₁ ⟶ a₂ := f.obj.left
  let m : a₂ ⟶ a₃ := g.obj.left
  let r : b₁ ⟶ b₂ := f.obj.right
  let n : b₂ ⟶ b₃ := g.obj.right
  let p : l ≫ t ⟶ s ≫ r := f.obj.cell
  let q : m ≫ u ⟶ t ≫ n := g.obj.cell
  change ((H.map₂ ((𝟙 (l ≫ m) ≫ 𝟙 _) ≫ 𝟙 _) ≫ (H.mapComp l m).hom) ▷ H.map u) ≫
      ((𝟙 (H.map l ≫ H.map m) ▷ H.map u) ≫
        (α_ (H.map l) (H.map m) (H.map u)).hom ≫
        H.map l ◁ ((H.mapComp m u).inv ≫ H.map₂ q ≫ (H.mapComp t n).hom) ≫
        (α_ (H.map l) (H.map t) (H.map n)).inv ≫
        ((H.mapComp l t).inv ≫ H.map₂ p ≫ (H.mapComp s r).hom) ▷ H.map n ≫
        (α_ (H.map s) (H.map r) (H.map n)).hom ≫
        (H.map s ◁ 𝟙 (H.map r ≫ H.map n))) =
    ((H.mapComp (l ≫ m) u).inv ≫
        H.map₂ ((𝟙 (l ≫ m) ▷ u) ≫ (α_ l m u).hom ≫ l ◁ q ≫
          (α_ l t n).inv ≫ p ▷ n ≫ (α_ s r n).hom ≫ (s ◁ 𝟙 (r ≫ n))) ≫
        (H.mapComp s (r ≫ n)).hom) ≫
      (H.map s ◁ (H.map₂ ((𝟙 (r ≫ n) ≫ 𝟙 _) ≫ 𝟙 _) ≫ (H.mapComp r n).hom))
  simpa only [Category.id_comp, Category.comp_id, H.map₂_id,
    Bicategory.id_whiskerRight, Bicategory.whiskerLeft_id] using
    mapCell_comp H s t u l m r n p q

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
          (mapComp H f h).inv := by
  intro S T U f g h η
  apply ObjectProperty.hom_ext
  exact ColaxComma.Hom₂.ext ((leftProjection H).map₂_whisker_left f η)
    ((rightProjection H).map₂_whisker_left f η)

/-- Mapping arrows preserves right whiskering through its composition comparisons. -/
private theorem map₂_whiskerRight (H : A ⥤ᵖ B) :
    ∀ {S T U : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
      {f g : S ⟶ T} (η : f ⟶ g) (h : T ⟶ U),
      (prelax H).map₂ (η ▷ h) =
        (mapComp H f h).hom ≫ (prelax H).map₂ η ▷ (prelax H).map h ≫
          (mapComp H g h).inv := by
  intro S T U f g η h
  apply ObjectProperty.hom_ext
  exact ColaxComma.Hom₂.ext ((leftProjection H).map₂_whisker_right η h)
    ((rightProjection H).map₂_whisker_right η h)

/-- Mapping arrows preserves associators through its composition comparisons. -/
private theorem map₂_associator (H : A ⥤ᵖ B) :
    ∀ {R S T U : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
      (f : R ⟶ S) (g : S ⟶ T) (h : T ⟶ U),
      (prelax H).map₂ (α_ f g h).hom =
        (mapComp H (f ≫ g) h).hom ≫
          (mapComp H f g).hom ▷ (prelax H).map h ≫
          (α_ ((prelax H).map f) ((prelax H).map g) ((prelax H).map h)).hom ≫
          (prelax H).map f ◁ (mapComp H g h).inv ≫
          (mapComp H f (g ≫ h)).inv := by
  intro R S T U f g h
  apply ObjectProperty.hom_ext
  exact ColaxComma.Hom₂.ext ((leftProjection H).map₂_associator f g h)
    ((rightProjection H).map₂_associator f g h)

/-- Mapping arrows preserves left unitors through its comparisons. -/
private theorem map₂_leftUnitor (H : A ⥤ᵖ B) :
    ∀ {S T : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
      (f : S ⟶ T),
      (prelax H).map₂ (λ_ f).hom =
        (mapComp H (𝟙 S) f).hom ≫
          (mapId H S).hom ▷ (prelax H).map f ≫
          (λ_ ((prelax H).map f)).hom := by
  intro S T f
  apply ObjectProperty.hom_ext
  exact ColaxComma.Hom₂.ext ((leftProjection H).map₂_left_unitor f)
    ((rightProjection H).map₂_left_unitor f)

/-- Mapping arrows preserves right unitors through its comparisons. -/
private theorem map₂_rightUnitor (H : A ⥤ᵖ B) :
    ∀ {S T : Bicategory.PseudoComma (Pseudofunctor.id A) (Pseudofunctor.id A)}
      (f : S ⟶ T),
      (prelax H).map₂ (ρ_ f).hom =
        (mapComp H f (𝟙 T)).hom ≫
          (prelax H).map f ◁ (mapId H T).hom ≫
          (ρ_ ((prelax H).map f)).hom := by
  intro S T f
  apply ObjectProperty.hom_ext
  exact ColaxComma.Hom₂.ext ((leftProjection H).map₂_right_unitor f)
    ((rightProjection H).map₂_right_unitor f)

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
from `H`, `PseudoComma.homMk`, and `PseudoComma.isoMk`.  The compatibility,
functoriality, and bicategorical coherence propositions are proved above. -/

end Pseudofunctor

end CategoryTheory
