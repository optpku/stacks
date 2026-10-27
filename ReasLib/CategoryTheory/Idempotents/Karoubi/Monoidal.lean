/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Idempotents.Karoubi
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.MonoidalCategory

universe v u

namespace CategoryTheory.Idempotents.Karoubi

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The tensor product of two formal images is the formal image of the tensor product
of their idempotents. -/
def monoidalTensorObj (P Q : Karoubi C) : Karoubi C where
  X := P.X ⊗ Q.X
  p := P.p ⊗ₘ Q.p
  idem := by simp

/-- The underlying object of the tensor of two formal images is the tensor of their
underlying objects. -/
theorem monoidalTensorObj_X (P Q : Karoubi C) :
    (monoidalTensorObj P Q).X = P.X ⊗ Q.X := rfl

/-- The projector of the tensor of two formal images is the tensor of their projectors. -/
theorem monoidalTensorObj_p (P Q : Karoubi C) :
    (monoidalTensorObj P Q).p = P.p ⊗ₘ Q.p := rfl

/-- Tensor two morphisms between formal images by tensoring their underlying morphisms. -/
def monoidalTensorHom {P₁ Q₁ P₂ Q₂ : Karoubi C} (f : P₁ ⟶ Q₁) (g : P₂ ⟶ Q₂) :
    monoidalTensorObj P₁ P₂ ⟶ monoidalTensorObj Q₁ Q₂ where
  f := f.f ⊗ₘ g.f
  comm := by
    simp only [monoidalTensorObj, tensorHom_comp_tensorHom, Hom.comm]

/-- The underlying morphism of the tensor of two formal-image morphisms is their
ambient tensor product. -/
theorem monoidalTensorHom_f {P₁ Q₁ P₂ Q₂ : Karoubi C}
    (f : P₁ ⟶ Q₁) (g : P₂ ⟶ Q₂) :
    (monoidalTensorHom f g).f = f.f ⊗ₘ g.f := rfl

/-- The tensor unit in the Karoubi envelope is the identity formal image of the
tensor unit of the original category. -/
def monoidalTensorUnit : Karoubi C where
  X := 𝟙_ C
  p := 𝟙 (𝟙_ C)
  idem := by simp

/-- The underlying object of the formal-image tensor unit is the ambient tensor unit. -/
theorem monoidalTensorUnit_X :
    (monoidalTensorUnit : Karoubi C).X = 𝟙_ C := rfl

/-- The projector of the formal-image tensor unit is the identity of the ambient
tensor unit. -/
theorem monoidalTensorUnit_p :
    (monoidalTensorUnit : Karoubi C).p = 𝟙 (𝟙_ C) := rfl

/-- The associator on formal images induced by the associator of the original category. -/
def monoidalAssociator (P Q R : Karoubi C) :
    monoidalTensorObj (monoidalTensorObj P Q) R ≅
      monoidalTensorObj P (monoidalTensorObj Q R) where
  hom :=
    { f := (monoidalTensorObj (monoidalTensorObj P Q) R).p ≫
        (α_ P.X Q.X R.X).hom ≫ (monoidalTensorObj P (monoidalTensorObj Q R)).p
      comm := by simp [monoidalTensorObj, Category.assoc] }
  inv :=
    { f := (monoidalTensorObj P (monoidalTensorObj Q R)).p ≫
        (α_ P.X Q.X R.X).inv ≫ (monoidalTensorObj (monoidalTensorObj P Q) R).p
      comm := by simp [monoidalTensorObj, Category.assoc] }
  hom_inv_id := by
    apply hom_ext
    dsimp
    simp [monoidalTensorObj, Category.assoc, idem, associator_naturality_assoc,
      associator_inv_naturality_assoc,
      -associator_conjugation]
  inv_hom_id := by
    apply hom_ext
    dsimp
    simp [monoidalTensorObj, Category.assoc, idem, associator_naturality_assoc,
      associator_inv_naturality_assoc,
      -associator_conjugation]

/-- The underlying hom of the formal-image associator is the ambient associator
sandwiched between the source and target projectors. -/
theorem monoidalAssociator_hom_f (P Q R : Karoubi C) :
    (monoidalAssociator P Q R).hom.f =
      (monoidalTensorObj (monoidalTensorObj P Q) R).p ≫
        (α_ P.X Q.X R.X).hom ≫ (monoidalTensorObj P (monoidalTensorObj Q R)).p := rfl

/-- The left unitor on a formal image induced by the left unitor of the original category. -/
def monoidalLeftUnitor (P : Karoubi C) :
    monoidalTensorObj monoidalTensorUnit P ≅ P where
  hom :=
    { f := (monoidalTensorObj monoidalTensorUnit P).p ≫ (λ_ P.X).hom ≫ P.p
      comm := by simp [monoidalTensorObj, monoidalTensorUnit, Category.assoc] }
  inv :=
    { f := P.p ≫ (λ_ P.X).inv ≫ (monoidalTensorObj monoidalTensorUnit P).p
      comm := by simp [monoidalTensorObj, monoidalTensorUnit, Category.assoc] }
  hom_inv_id := by
    apply hom_ext
    dsimp
    simp [monoidalTensorObj, monoidalTensorUnit, Category.assoc, idem]
  inv_hom_id := by
    apply hom_ext
    dsimp
    simp [monoidalTensorObj, monoidalTensorUnit, Category.assoc, idem]

/-- The underlying hom of the formal-image left unitor is the ambient left unitor
sandwiched between the source and target projectors. -/
theorem monoidalLeftUnitor_hom_f (P : Karoubi C) :
    (monoidalLeftUnitor P).hom.f =
      (monoidalTensorObj monoidalTensorUnit P).p ≫ (λ_ P.X).hom ≫ P.p := rfl

/-- The right unitor on a formal image induced by the right unitor of the original category. -/
def monoidalRightUnitor (P : Karoubi C) :
    monoidalTensorObj P monoidalTensorUnit ≅ P where
  hom :=
    { f := (monoidalTensorObj P monoidalTensorUnit).p ≫ (ρ_ P.X).hom ≫ P.p
      comm := by simp [monoidalTensorObj, monoidalTensorUnit, Category.assoc] }
  inv :=
    { f := P.p ≫ (ρ_ P.X).inv ≫ (monoidalTensorObj P monoidalTensorUnit).p
      comm := by simp [monoidalTensorObj, monoidalTensorUnit, Category.assoc] }
  hom_inv_id := by
    apply hom_ext
    dsimp
    simp [monoidalTensorObj, monoidalTensorUnit, Category.assoc, idem]
  inv_hom_id := by
    apply hom_ext
    dsimp
    simp [monoidalTensorObj, monoidalTensorUnit, Category.assoc, idem]

/-- The underlying hom of the formal-image right unitor is the ambient right unitor
sandwiched between the source and target projectors. -/
theorem monoidalRightUnitor_hom_f (P : Karoubi C) :
    (monoidalRightUnitor P).hom.f =
      (monoidalTensorObj P monoidalTensorUnit).p ≫ (ρ_ P.X).hom ≫ P.p := rfl

/-- The tensor product, tensor unit, associator, and unitors on the Karoubi envelope. -/
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (Karoubi C) where
  tensorObj := monoidalTensorObj
  whiskerLeft := fun P {_ _} f ↦ monoidalTensorHom (𝟙 P) f
  whiskerRight := fun {_ _} f Q ↦ monoidalTensorHom f (𝟙 Q)
  tensorHom := monoidalTensorHom
  tensorUnit := monoidalTensorUnit
  associator := monoidalAssociator
  leftUnitor := monoidalLeftUnitor
  rightUnitor := monoidalRightUnitor

/-- The projected tensor operations satisfy the monoidal naturality and coherence laws. -/
instance instMonoidalCategory : MonoidalCategory (Karoubi C) where
  tensorHom_def := by
    intros
    apply hom_ext
    simp [tensorHom, tensorObj, whiskerLeft, whiskerRight, monoidalTensorHom, monoidalTensorObj]
  id_tensorHom_id := by
    intros
    rfl
  tensorHom_comp_tensorHom := by
    intros
    apply hom_ext
    simp [tensorHom, tensorObj, monoidalTensorHom, monoidalTensorObj]
  whiskerLeft_id := by
    intros
    rfl
  id_whiskerRight := by
    intros
    rfl
  associator_naturality := by
    intros
    apply hom_ext
    simp [tensorHom, tensorObj, associator, monoidalTensorHom, monoidalTensorObj,
      monoidalAssociator, Category.assoc, associator_naturality_assoc, -associator_conjugation]
  leftUnitor_naturality := by
    intros
    apply hom_ext
    simp [tensorObj, whiskerLeft, leftUnitor, tensorUnit, monoidalTensorHom, monoidalTensorObj,
      monoidalTensorUnit, monoidalLeftUnitor, Category.assoc]
  rightUnitor_naturality := by
    intros
    apply hom_ext
    simp [tensorObj, whiskerRight, rightUnitor, tensorUnit, monoidalTensorHom, monoidalTensorObj,
      monoidalTensorUnit, monoidalRightUnitor, Category.assoc]
  pentagon := by
    intros
    apply hom_ext
    dsimp [whiskerLeft, whiskerRight, associator, leftUnitor, rightUnitor,
      tensorObj, tensorUnit, instMonoidalCategoryStruct, monoidalTensorHom, monoidalTensorObj, monoidalAssociator]
    -- Move the projectors to the target before applying the ambient coherence law.
    simp only [associator_naturality_assoc, tensorHom_comp_tensorHom, idem, Category.assoc]
    simp only [← whiskerRight_comp_tensorHom, ← whiskerLeft_comp_tensorHom, Category.assoc,
      associator_naturality_assoc, tensorHom_comp_whiskerLeft_assoc, associator_naturality,
      tensorHom_comp_tensorHom, idem, pentagon_assoc]
  triangle := by
    intros
    apply hom_ext
    dsimp [whiskerLeft, whiskerRight, associator, leftUnitor, rightUnitor,
      tensorObj, tensorUnit, instMonoidalCategoryStruct, monoidalTensorHom, monoidalTensorObj, monoidalAssociator, monoidalTensorUnit, monoidalLeftUnitor, monoidalRightUnitor]
    simp only [tensorHom_id, id_tensorHom, leftUnitor_naturality_assoc, idem, Category.assoc,
      tensorHom_comp_tensorHom]
    simp only [← whiskerLeft_comp_tensorHom, triangle_assoc, tensorHom_comp_whiskerRight_assoc, ←
      whiskerRight_comp_tensorHom, Category.assoc, tensorHom_comp_tensorHom, idem]

variable [SymmetricCategory C]

/-- The braiding on formal images induced by the braiding of the original category. -/
def monoidalBraiding (P Q : Karoubi C) :
    monoidalTensorObj P Q ≅ monoidalTensorObj Q P where
  hom :=
    { f := (monoidalTensorObj P Q).p ≫ (β_ P.X Q.X).hom ≫ (monoidalTensorObj Q P).p
      comm := by simp [monoidalTensorObj, Category.assoc] }
  inv :=
    { f := (monoidalTensorObj Q P).p ≫ (β_ P.X Q.X).inv ≫ (monoidalTensorObj P Q).p
      comm := by simp [monoidalTensorObj, Category.assoc] }
  hom_inv_id := by
    apply hom_ext
    dsimp
    simp [monoidalTensorObj, Category.assoc, idem,
      BraidedCategory.braiding_naturality_assoc,
      BraidedCategory.braiding_inv_naturality_assoc]
  inv_hom_id := by
    apply hom_ext
    dsimp
    simp [monoidalTensorObj, Category.assoc, idem,
      BraidedCategory.braiding_naturality_assoc,
      BraidedCategory.braiding_inv_naturality_assoc]

/-- The underlying hom of the formal-image braiding is the ambient braiding
sandwiched between the source and target projectors. -/
theorem monoidalBraiding_hom_f (P Q : Karoubi C) :
    (monoidalBraiding P Q).hom.f =
      (monoidalTensorObj P Q).p ≫ (β_ P.X Q.X).hom ≫ (monoidalTensorObj Q P).p := rfl

/-- A symmetric monoidal structure on a category induces one on its Karoubi envelope. -/
instance instSymmetricCategory : SymmetricCategory (Karoubi C) where
  braiding := monoidalBraiding
  braiding_naturality_right := by
    intros
    apply hom_ext
    simp [tensorObj, whiskerLeft, whiskerRight, monoidalTensorHom, monoidalTensorObj,
      monoidalBraiding, Category.assoc, BraidedCategory.braiding_naturality_assoc]
  braiding_naturality_left := by
    intros
    apply hom_ext
    simp [tensorObj, whiskerLeft, whiskerRight, monoidalTensorHom, monoidalTensorObj,
      monoidalBraiding, Category.assoc, BraidedCategory.braiding_naturality_assoc]
  hexagon_forward := by
    intros
    apply hom_ext
    dsimp [whiskerLeft, whiskerRight, associator, leftUnitor, rightUnitor,
      tensorObj, tensorUnit, instMonoidalCategoryStruct, monoidalTensorHom, monoidalTensorObj, monoidalAssociator, monoidalBraiding]
    simp only [associator_naturality_assoc, tensorHom_comp_tensorHom, idem,
      BraidedCategory.braiding_naturality_assoc, Category.assoc]
    simp only [BraidedCategory.hexagon_forward_assoc, ← whiskerRight_comp_tensorHom, ←
      whiskerLeft_comp_tensorHom, Category.assoc, associator_naturality_assoc,
      tensorHom_comp_whiskerLeft_assoc, BraidedCategory.braiding_naturality,
      tensorHom_comp_tensorHom, idem]
  hexagon_reverse := by
    intros
    apply hom_ext
    dsimp [whiskerLeft, whiskerRight, associator, leftUnitor, rightUnitor,
      tensorObj, tensorUnit, instMonoidalCategoryStruct, monoidalTensorHom, monoidalTensorObj, monoidalAssociator, monoidalBraiding]
    simp only [associator_inv_naturality_assoc, tensorHom_comp_tensorHom, idem,
      BraidedCategory.braiding_naturality_assoc, Category.assoc]
    simp only [BraidedCategory.hexagon_reverse_assoc, ← whiskerLeft_comp_tensorHom, ←
      whiskerRight_comp_tensorHom, Category.assoc, associator_inv_naturality_assoc,
      tensorHom_comp_whiskerRight_assoc, BraidedCategory.braiding_naturality,
      tensorHom_comp_tensorHom, idem]
  symmetry := by
    intros
    apply hom_ext
    simp [tensorObj, monoidalTensorObj, monoidalBraiding, Category.assoc,
      BraidedCategory.braiding_naturality_assoc]

end CategoryTheory.Idempotents.Karoubi
