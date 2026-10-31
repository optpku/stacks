/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Category.PreorderWithAdjoinedIdentities
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

@[expose] public section

noncomputable section

universe u v w

namespace CategoryTheory.PreorderWithAdjoinedIdentities

open CategoryTheory.Limits

variable {I : Type u} [Preorder I] {C : Type v} [Category.{w} C]
variable (D : PreorderWithAdjoinedIdentities I ⥤ C)

/-- The images of two consecutive preorder transitions compose to the image of their composite. -/
@[reassoc (attr := simp)]
theorem map_transition_comp {first second third : I}
    (firstLe : first ≤ second) (secondLe : second ≤ third) :
    D.map (transition firstLe) ≫ D.map (transition secondLe) =
      D.map (transition (le_trans firstLe secondLe)) :=
  (D.map_comp (transition firstLe) (transition secondLe)).symm

/-- The image of a reflexive transition is idempotent. -/
theorem retractionCondition (index : I) :
    D.map (transition (le_refl index)) ≫ D.map (transition (le_refl index)) =
      D.map (transition (le_refl index)) ≫ 𝟙 (D.obj index) := by
  simpa only [Category.comp_id] using map_transition_comp D (le_refl index) (le_refl index)

variable [HasEqualizers C]

/-- The reflexive transition factors through its equalizer with the identity. -/
def retraction (index : I) :
    D.obj index ⟶ equalizer (D.map (transition (le_refl index))) (𝟙 (D.obj index)) :=
  equalizer.lift (D.map (transition (le_refl index))) (retractionCondition D index)

/-- The retraction followed by the equalizer inclusion is the reflexive transition. -/
@[reassoc (attr := simp)]
theorem retraction_ι (index : I) :
    retraction D index ≫
      equalizer.ι (D.map (transition (le_refl index))) (𝟙 (D.obj index)) =
        D.map (transition (le_refl index)) :=
  equalizer.lift_ι _ _

/-- The equalizer inclusion followed by the reflexive-transition retraction is the identity. -/
theorem inclusion_retraction (index : I) :
    equalizer.ι (D.map (transition (le_refl index))) (𝟙 (D.obj index)) ≫
      retraction D index = 𝟙 _ := by
  apply equalizer.hom_ext
  simp only [Category.assoc, retraction_ι, Category.id_comp]
  simpa only [Category.comp_id] using
    equalizer.condition (D.map (transition (le_refl index))) (𝟙 (D.obj index))

/-- Splitting reflexive transition idempotents produces an ordinary preorder diagram. -/
def normalize : I ⥤ C where
  obj index := equalizer (D.map (transition (le_refl index))) (𝟙 (D.obj index))
  map {first second} arrow :=
    equalizer.ι (D.map (transition (le_refl first))) (𝟙 (D.obj first)) ≫
      D.map (transition (leOfHom arrow)) ≫ retraction D second
  map_id index := by
    change equalizer.ι _ _ ≫ D.map (transition (le_refl index)) ≫ retraction D index = 𝟙 _
    rw [← Category.assoc, equalizer.condition, Category.comp_id, inclusion_retraction]
  map_comp firstArrow secondArrow := by
    simp only [Category.assoc, retraction_ι_assoc, map_transition_comp_assoc]

/-- Restricting raw cocone legs to the equalizers gives a cocone over the normalized diagram. -/
def normalizedCocone (cocone : Cocone D) : Cocone (normalize D) where
  pt := cocone.pt
  ι :=
    { app := fun index =>
        equalizer.ι (D.map (transition (le_refl index))) (𝟙 (D.obj index)) ≫
          cocone.ι.app index
      naturality := by
        intro first second arrow
        let inclusion :=
          equalizer.ι (D.map (transition (le_refl first))) (𝟙 (D.obj first))
        change (inclusion ≫ D.map (transition (leOfHom arrow)) ≫ retraction D second) ≫
            (equalizer.ι _ _ ≫ cocone.ι.app second) =
          (inclusion ≫ cocone.ι.app first) ≫ 𝟙 cocone.pt
        calc
          _ = inclusion ≫ D.map (transition (leOfHom arrow)) ≫
              (retraction D second ≫ equalizer.ι _ _) ≫ cocone.ι.app second := by
            simp only [Category.assoc]
          _ = inclusion ≫ D.map (transition (leOfHom arrow)) ≫
              D.map (transition (le_refl second)) ≫ cocone.ι.app second :=
            congrArg (fun k => inclusion ≫ D.map (transition (leOfHom arrow)) ≫
              k ≫ cocone.ι.app second) (retraction_ι D second)
          _ = inclusion ≫ D.map (transition (leOfHom arrow)) ≫ cocone.ι.app second :=
            congrArg (inclusion ≫ D.map (transition (leOfHom arrow)) ≫ ·)
              (cocone.w (transition (le_refl second)))
          _ = inclusion ≫ cocone.ι.app first :=
            congrArg (inclusion ≫ ·) (cocone.w (transition (leOfHom arrow)))
          _ = _ := (Category.comp_id _).symm }

/-- Composing normalized cocone legs with retractions gives a cocone over the raw diagram. -/
def denormalizedCocone (cocone : Cocone (normalize D)) : Cocone D where
  pt := cocone.pt
  ι :=
    { app := fun index => retraction D index ≫ cocone.ι.app index
      naturality := by
        intro first second arrow
        rcases arrow with equality | inequality
        · obtain ⟨rfl⟩ := equality
          change D.map (𝟙 first) ≫ (retraction D first ≫ cocone.ι.app first) =
            (retraction D first ≫ cocone.ι.app first) ≫ 𝟙 cocone.pt
          exact (congrArg (· ≫ (retraction D first ≫ cocone.ι.app first))
            (D.map_id first)).trans
              ((Category.id_comp _).trans (Category.comp_id _).symm)
        · obtain ⟨h⟩ := inequality
          change D.map (transition h) ≫ (retraction D second ≫ cocone.ι.app second) =
            (retraction D first ≫ cocone.ι.app first) ≫ 𝟙 cocone.pt
          calc
            _ = D.map (transition (le_refl (α := I) first)) ≫ D.map (transition h) ≫
                retraction D second ≫ cocone.ι.app second :=
              (congrArg (· ≫ retraction D second ≫ cocone.ι.app second)
                (map_transition_comp D (le_refl (α := I) first) h).symm).trans
                  (Category.assoc _ _ _)
            _ = retraction D first ≫ equalizer.ι _ _ ≫ D.map (transition h) ≫
                retraction D second ≫ cocone.ι.app second :=
              (retraction_ι_assoc D first
                (D.map (transition h) ≫ retraction D second ≫ cocone.ι.app second)).symm
            _ = retraction D first ≫
                ((normalize D).map (homOfLE h) ≫ cocone.ι.app second) := by
              simp only [normalize, Category.assoc]
            _ = retraction D first ≫ cocone.ι.app first :=
              congrArg (retraction D first ≫ ·) (cocone.w (homOfLE h))
            _ = _ := (Category.comp_id _).symm }

/-- The colimit of the normalized diagram is canonically isomorphic to the raw colimit. -/
def colimitIso [HasColimit D] [HasColimit (normalize D)] :
    colimit (normalize D) ≅ colimit D where
  hom := colimit.desc (normalize D) (normalizedCocone D (colimit.cocone D))
  inv := colimit.desc D (denormalizedCocone D (colimit.cocone (normalize D)))
  hom_inv_id := by
    apply colimit.hom_ext
    intro index
    let inclusion : (normalize D).obj index ⟶ D.obj index :=
      equalizer.ι (D.map (transition (le_refl index))) (𝟙 (D.obj index))
    calc
      _ = (inclusion ≫ colimit.ι D index) ≫
          colimit.desc D (denormalizedCocone D (colimit.cocone (normalize D))) :=
        colimit.ι_desc_assoc (normalizedCocone D (colimit.cocone D)) index _
      _ = inclusion ≫ (retraction D index ≫ colimit.ι (normalize D) index) :=
        (Category.assoc _ _ _).trans
          (congrArg (inclusion ≫ ·)
            (colimit.ι_desc (denormalizedCocone D (colimit.cocone (normalize D))) index))
      _ = (inclusion ≫ retraction D index) ≫ colimit.ι (normalize D) index :=
        (Category.assoc _ _ _).symm
      _ = colimit.ι (normalize D) index :=
        (congrArg (· ≫ colimit.ι (normalize D) index) (inclusion_retraction D index)).trans
          (Category.id_comp _)
      _ = _ := (Category.comp_id _).symm
  inv_hom_id := by
    apply colimit.hom_ext
    intro index
    calc
      _ = (retraction D index ≫ colimit.ι (normalize D) index) ≫
          colimit.desc (normalize D) (normalizedCocone D (colimit.cocone D)) :=
        colimit.ι_desc_assoc (denormalizedCocone D (colimit.cocone (normalize D))) index _
      _ = retraction D index ≫ (equalizer.ι _ _ ≫ colimit.ι D index) :=
        (Category.assoc _ _ _).trans
          (congrArg (retraction D index ≫ ·)
            (colimit.ι_desc (normalizedCocone D (colimit.cocone D)) index))
      _ = (retraction D index ≫ equalizer.ι _ _) ≫ colimit.ι D index :=
        (Category.assoc _ _ _).symm
      _ = D.map (transition (le_refl (α := I) index)) ≫ colimit.ι D index :=
        congrArg (· ≫ colimit.ι D index) (retraction_ι D index)
      _ = colimit.ι D index := colimit.w D (transition (le_refl (α := I) index))
      _ = _ := (Category.comp_id _).symm

/-- A stage whose reflexive transition is the identity is unchanged by normalization. -/
theorem inclusion_isIso (index : I)
    (identityTransition : D.map (transition (le_refl index)) = 𝟙 (D.obj index)) :
    IsIso (equalizer.ι (D.map (transition (le_refl index))) (𝟙 (D.obj index))) :=
  equalizer.ι_of_eq identityTransition

end CategoryTheory.PreorderWithAdjoinedIdentities
