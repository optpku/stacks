module

public import ReasLib.CategoryTheory.Monoidal.RightInternalHom.Computation

/-!
# Enriched-category laws for chosen right internal Homs

This leaf records the normal forms and unit/associativity laws for identity, composition, left
tensoring, and the braided composition transpose.
-/

@[expose] public section

universe v u

namespace CategoryTheory.RightInternalHom

open MonoidalCategory
open scoped CategoryTheory.RightInternalHom

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable (H : RightInternalHom C)

set_option backward.isDefEq.respectTransparency false

/-- Uncurrying the internal-Hom identity recovers the left unitor. -/
@[simp]
theorem uncurry_id (X : C) :
    H.uncurry (H.id X) = (λ_ X).hom := by
  exact H.uncurry_curry (λ_ X).hom

/-- Currying evaluation gives the identity of the internal-Hom object. -/
@[simp]
theorem curry_ev (X Y : C) :
    H.curry (H.ev X Y) = 𝟙 (X ⟶[H]ᵣ Y) := by
  rw [← H.uncurry_id_eq_ev X Y]
  exact H.curry_uncurry (𝟙 (X ⟶[H]ᵣ Y))

/-- Uncurrying internal-Hom composition gives the double-evaluation composite. -/
@[simp]
theorem uncurry_comp (X Y Z : C) :
    H.uncurry (H.comp X Y Z) =
      (α_ (Y ⟶[H]ᵣ Z) (X ⟶[H]ᵣ Y) X).hom ≫
        ((Y ⟶[H]ᵣ Z) ◁ H.ev X Y) ≫ H.ev Y Z := by
  exact H.uncurry_curry _

/-- Uncurrying `tensorLeft` gives evaluation after reassociating the three tensor factors. -/
@[simp]
theorem uncurry_tensorLeft (X Y Z : C) :
    H.uncurry (H.tensorLeft X Y Z) =
      (α_ Z (X ⟶[H]ᵣ Y) X).hom ≫ (Z ◁ H.ev X Y) := by
  exact H.uncurry_curry _

/-- Composition with the internal-Hom identity of the source is a right unit. -/
@[reassoc]
theorem comp_id_right (X Y : C) :
    (ρ_ (X ⟶[H]ᵣ Y)).inv ≫
        ((X ⟶[H]ᵣ Y) ◁ H.id X) ≫ H.comp X X Y =
      𝟙 (X ⟶[H]ᵣ Y) := by
  apply H.uncurry_injective
  rw [H.uncurry_natural_left, H.uncurry_natural_left]
  rw [H.uncurry_comp, H.uncurry_id_eq_ev]
  rw [MonoidalCategory.associator_naturality_middle_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [← H.uncurry_eq, H.uncurry_id]
  rw [MonoidalCategory.triangle_assoc_comp_right_inv_assoc]
  simp

/-- Composition with the internal-Hom identity of the target is a left unit. -/
@[reassoc]
theorem comp_id_left (X Y : C) :
    (λ_ (X ⟶[H]ᵣ Y)).inv ≫
        H.id Y ▷ (X ⟶[H]ᵣ Y) ≫ H.comp X Y Y =
      𝟙 (X ⟶[H]ᵣ Y) := by
  apply H.uncurry_injective
  rw [H.uncurry_natural_left, H.uncurry_natural_left]
  rw [H.uncurry_comp, H.uncurry_id_eq_ev]
  rw [MonoidalCategory.associator_naturality_left_assoc]
  rw [MonoidalCategory.leftUnitor_inv_whiskerRight_assoc]
  simp only [Iso.inv_hom_id_assoc]
  rw [← MonoidalCategory.whisker_exchange_assoc]
  rw [← MonoidalCategory.leftUnitor_inv_naturality_assoc]
  rw [← H.uncurry_eq, H.uncurry_id]
  simp

/-- Internal-Hom composition is associative after the canonical tensor reassociation. -/
@[reassoc]
theorem comp_assoc (W X Y Z : C) :
    (H.comp Y Z W ▷ (X ⟶[H]ᵣ Y)) ≫ H.comp X Y W =
      (α_ (Z ⟶[H]ᵣ W) (Y ⟶[H]ᵣ Z) (X ⟶[H]ᵣ Y)).hom ≫
        ((Z ⟶[H]ᵣ W) ◁ H.comp X Y Z) ≫ H.comp X Z W := by
  apply H.uncurry_injective
  rw [H.uncurry_natural_left]
  rw [H.uncurry_natural_left, H.uncurry_natural_left]
  rw [H.uncurry_comp, H.uncurry_comp]
  rw [MonoidalCategory.associator_naturality_left_assoc]
  rw [← MonoidalCategory.whisker_exchange_assoc]
  rw [← H.uncurry_eq, H.uncurry_comp]
  rw [MonoidalCategory.associator_naturality_middle_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [← H.uncurry_eq, H.uncurry_comp]
  monoidal

section Braided

variable [BraidedCategory C]

/-- Uncurrying the composition transpose gives the braided double-evaluation composite used in
its definition. -/
@[simp]
theorem uncurry_compTranspose (X Y Z : C) :
    H.uncurry (H.compTranspose X Y Z) =
      (α_ (Y ⟶[H]ᵣ Z) X (X ⟶[H]ᵣ Y)).hom ≫
        ((Y ⟶[H]ᵣ Z) ◁ (β_ X (X ⟶[H]ᵣ Y)).hom) ≫
        ((Y ⟶[H]ᵣ Z) ◁ H.ev X Y) ≫ H.ev Y Z := by
  exact H.uncurry_curry _

end Braided

end CategoryTheory.RightInternalHom
