/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Idempotents.Karoubi
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.MonoidalCategory

universe v u

namespace CategoryTheory.Idempotents.Karoubi

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- The tensor product of two formal images is the formal image of the tensor product
of their idempotents. -/
def monoidalTensorObj (P Q : Karoubi C) : Karoubi C where
  X := P.X ⊗ Q.X
  p := P.p ⊗ₘ Q.p
  idem := sorry

/-- The underlying object of the tensor of two formal images is the tensor of their
underlying objects. -/
theorem monoidalTensorObj_X (P Q : Karoubi C) :
    (monoidalTensorObj P Q).X = P.X ⊗ Q.X := sorry

/-- The projector of the tensor of two formal images is the tensor of their projectors. -/
theorem monoidalTensorObj_p (P Q : Karoubi C) :
    (monoidalTensorObj P Q).p = P.p ⊗ₘ Q.p := sorry

/-- Tensor two morphisms between formal images by tensoring their underlying morphisms. -/
def monoidalTensorHom {P₁ Q₁ P₂ Q₂ : Karoubi C} (f : P₁ ⟶ Q₁) (g : P₂ ⟶ Q₂) :
    monoidalTensorObj P₁ P₂ ⟶ monoidalTensorObj Q₁ Q₂ where
  f := f.f ⊗ₘ g.f
  comm := sorry

/-- The underlying morphism of the tensor of two formal-image morphisms is their
ambient tensor product. -/
theorem monoidalTensorHom_f {P₁ Q₁ P₂ Q₂ : Karoubi C}
    (f : P₁ ⟶ Q₁) (g : P₂ ⟶ Q₂) :
    (monoidalTensorHom f g).f = f.f ⊗ₘ g.f := sorry

/-- The tensor unit in the Karoubi envelope is the identity formal image of the
tensor unit of the original category. -/
def monoidalTensorUnit : Karoubi C where
  X := 𝟙_ C
  p := 𝟙 (𝟙_ C)
  idem := sorry

/-- The underlying object of the formal-image tensor unit is the ambient tensor unit. -/
theorem monoidalTensorUnit_X :
    (monoidalTensorUnit : Karoubi C).X = 𝟙_ C := sorry

/-- The projector of the formal-image tensor unit is the identity of the ambient
tensor unit. -/
theorem monoidalTensorUnit_p :
    (monoidalTensorUnit : Karoubi C).p = 𝟙 (𝟙_ C) := sorry

/-- The associator on formal images induced by the associator of the original category. -/
def monoidalAssociator (P Q R : Karoubi C) :
    monoidalTensorObj (monoidalTensorObj P Q) R ≅
      monoidalTensorObj P (monoidalTensorObj Q R) where
  hom :=
    { f := (monoidalTensorObj (monoidalTensorObj P Q) R).p ≫
        (α_ P.X Q.X R.X).hom ≫ (monoidalTensorObj P (monoidalTensorObj Q R)).p
      comm := sorry }
  inv :=
    { f := (monoidalTensorObj P (monoidalTensorObj Q R)).p ≫
        (α_ P.X Q.X R.X).inv ≫ (monoidalTensorObj (monoidalTensorObj P Q) R).p
      comm := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying hom of the formal-image associator is the ambient associator
sandwiched between the source and target projectors. -/
theorem monoidalAssociator_hom_f (P Q R : Karoubi C) :
    (monoidalAssociator P Q R).hom.f =
      (monoidalTensorObj (monoidalTensorObj P Q) R).p ≫
        (α_ P.X Q.X R.X).hom ≫ (monoidalTensorObj P (monoidalTensorObj Q R)).p := sorry

/-- The left unitor on a formal image induced by the left unitor of the original category. -/
def monoidalLeftUnitor (P : Karoubi C) :
    monoidalTensorObj monoidalTensorUnit P ≅ P where
  hom :=
    { f := (monoidalTensorObj monoidalTensorUnit P).p ≫ (λ_ P.X).hom ≫ P.p
      comm := sorry }
  inv :=
    { f := P.p ≫ (λ_ P.X).inv ≫ (monoidalTensorObj monoidalTensorUnit P).p
      comm := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying hom of the formal-image left unitor is the ambient left unitor
sandwiched between the source and target projectors. -/
theorem monoidalLeftUnitor_hom_f (P : Karoubi C) :
    (monoidalLeftUnitor P).hom.f =
      (monoidalTensorObj monoidalTensorUnit P).p ≫ (λ_ P.X).hom ≫ P.p := sorry

/-- The right unitor on a formal image induced by the right unitor of the original category. -/
def monoidalRightUnitor (P : Karoubi C) :
    monoidalTensorObj P monoidalTensorUnit ≅ P where
  hom :=
    { f := (monoidalTensorObj P monoidalTensorUnit).p ≫ (ρ_ P.X).hom ≫ P.p
      comm := sorry }
  inv :=
    { f := P.p ≫ (ρ_ P.X).inv ≫ (monoidalTensorObj P monoidalTensorUnit).p
      comm := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying hom of the formal-image right unitor is the ambient right unitor
sandwiched between the source and target projectors. -/
theorem monoidalRightUnitor_hom_f (P : Karoubi C) :
    (monoidalRightUnitor P).hom.f =
      (monoidalTensorObj P monoidalTensorUnit).p ≫ (ρ_ P.X).hom ≫ P.p := sorry

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
  tensorHom_def := sorry
  id_tensorHom_id := sorry
  tensorHom_comp_tensorHom := sorry
  whiskerLeft_id := sorry
  id_whiskerRight := sorry
  associator_naturality := sorry
  leftUnitor_naturality := sorry
  rightUnitor_naturality := sorry
  pentagon := sorry
  triangle := sorry

variable [SymmetricCategory C]

/-- The braiding on formal images induced by the braiding of the original category. -/
def monoidalBraiding (P Q : Karoubi C) :
    monoidalTensorObj P Q ≅ monoidalTensorObj Q P where
  hom :=
    { f := (monoidalTensorObj P Q).p ≫ (β_ P.X Q.X).hom ≫ (monoidalTensorObj Q P).p
      comm := sorry }
  inv :=
    { f := (monoidalTensorObj Q P).p ≫ (β_ P.X Q.X).inv ≫ (monoidalTensorObj P Q).p
      comm := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The underlying hom of the formal-image braiding is the ambient braiding
sandwiched between the source and target projectors. -/
theorem monoidalBraiding_hom_f (P Q : Karoubi C) :
    (monoidalBraiding P Q).hom.f =
      (monoidalTensorObj P Q).p ≫ (β_ P.X Q.X).hom ≫ (monoidalTensorObj Q P).p := sorry

/-- A symmetric monoidal structure on a category induces one on its Karoubi envelope. -/
instance instSymmetricCategory : SymmetricCategory (Karoubi C) where
  braiding := monoidalBraiding
  braiding_naturality_right := sorry
  braiding_naturality_left := sorry
  hexagon_forward := sorry
  hexagon_reverse := sorry
  symmetry := sorry

end CategoryTheory.Idempotents.Karoubi
