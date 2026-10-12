/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

/-- The image of a reflexive transition is idempotent. -/
theorem retractionCondition (index : I) :
    D.map (transition (le_refl index)) ≫ D.map (transition (le_refl index)) =
      D.map (transition (le_refl index)) ≫ 𝟙 (D.obj index) := sorry

variable [HasEqualizers C]

/-- The reflexive transition factors through its equalizer with the identity. -/
def retraction (index : I) :
    D.obj index ⟶ equalizer (D.map (transition (le_refl index))) (𝟙 (D.obj index)) :=
  equalizer.lift (D.map (transition (le_refl index))) (retractionCondition D index)

/-- The equalizer inclusion followed by the reflexive-transition retraction is the identity. -/
theorem inclusion_retraction (index : I) :
    equalizer.ι (D.map (transition (le_refl index))) (𝟙 (D.obj index)) ≫
      retraction D index = 𝟙 _ := sorry

/-- Splitting reflexive transition idempotents produces an ordinary preorder diagram. -/
def normalize : I ⥤ C where
  obj index := equalizer (D.map (transition (le_refl index))) (𝟙 (D.obj index))
  map {first second} arrow :=
    equalizer.ι (D.map (transition (le_refl first))) (𝟙 (D.obj first)) ≫
      D.map (transition (leOfHom arrow)) ≫ retraction D second
  map_id := sorry
  map_comp := sorry

/-- Restricting raw cocone legs to the equalizers gives a cocone over the normalized diagram. -/
def normalizedCocone (cocone : Cocone D) : Cocone (normalize D) where
  pt := cocone.pt
  ι :=
    { app := fun index =>
        equalizer.ι (D.map (transition (le_refl index))) (𝟙 (D.obj index)) ≫
          cocone.ι.app index
      naturality := sorry }

/-- Composing normalized cocone legs with retractions gives a cocone over the raw diagram. -/
def denormalizedCocone (cocone : Cocone (normalize D)) : Cocone D where
  pt := cocone.pt
  ι :=
    { app := fun index => retraction D index ≫ cocone.ι.app index
      naturality := sorry }

/-- The colimit of the normalized diagram is canonically isomorphic to the raw colimit. -/
def colimitIso [HasColimit D] [HasColimit (normalize D)] :
    colimit (normalize D) ≅ colimit D where
  hom := colimit.desc (normalize D) (normalizedCocone D (colimit.cocone D))
  inv := colimit.desc D (denormalizedCocone D (colimit.cocone (normalize D)))
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- A stage whose reflexive transition is the identity is unchanged by normalization. -/
theorem inclusion_isIso (index : I)
    (identityTransition : D.map (transition (le_refl index)) = 𝟙 (D.obj index)) :
    IsIso (equalizer.ι (D.map (transition (le_refl index))) (𝟙 (D.obj index))) := sorry

end CategoryTheory.PreorderWithAdjoinedIdentities
