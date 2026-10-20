module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Cospan.Basic.Core

/-!
# Modifications of based cospan transformations

This file defines modifications between universe-polymorphic based cospan transformations,
their category structure, and evaluation at the three vertices of a cospan.
-/

@[expose] public section

namespace CategoryTheory

open BasedFunctor

universe u v
universe uX₁ vX₁ uY₁ vY₁ uS₁ vS₁
universe uX₂ vX₂ uY₂ vY₂ uS₂ vS₂

variable {C : Type u} [Category.{v} C]
variable {X₁ : BasedCategory.{vX₁, uX₁} C}
variable {Y₁ : BasedCategory.{vY₁, uY₁} C}
variable {S₁ : BasedCategory.{vS₁, uS₁} C}
variable {X₂ : BasedCategory.{vX₂, uX₂} C}
variable {Y₂ : BasedCategory.{vY₂, uY₂} C}
variable {S₂ : BasedCategory.{vS₂, uS₂} C}

namespace BasedCospanTransform

variable {F₁ : X₁ ⥤ᵇ S₁} {G₁ : Y₁ ⥤ᵇ S₁}
variable {F₂ : X₂ ⥤ᵇ S₂} {G₂ : Y₂ ⥤ᵇ S₂}

/-- A modification between based cospan transformations. It consists of based natural
transformations at the three vertices satisfying the two generating naturality squares. -/
def Hom (psi phi : BasedCospanTransform F₁ G₁ F₂ G₂) :=
  { components : (psi.left ⟶ phi.left) × (psi.right ⟶ phi.right) ×
      (psi.base ⟶ phi.base) //
    (BasedCategory.whiskerRight components.1 F₂ ≫ phi.leftIso.hom =
      psi.leftIso.hom ≫ BasedCategory.whiskerLeft F₁ components.2.2) ∧
    (BasedCategory.whiskerRight components.2.1 G₂ ≫ phi.rightIso.hom =
      psi.rightIso.hom ≫ BasedCategory.whiskerLeft G₁ components.2.2) }

namespace Hom

variable {psi phi chi : BasedCospanTransform F₁ G₁ F₂ G₂}

/-- Construct a modification from three vertex transformations satisfying the two cospan
naturality equations. -/
def mk (left : psi.left ⟶ phi.left) (right : psi.right ⟶ phi.right)
    (base : psi.base ⟶ phi.base)
    (leftNaturality :
      BasedCategory.whiskerRight left F₂ ≫ phi.leftIso.hom =
        psi.leftIso.hom ≫ BasedCategory.whiskerLeft F₁ base)
    (rightNaturality :
      BasedCategory.whiskerRight right G₂ ≫ phi.rightIso.hom =
        psi.rightIso.hom ≫ BasedCategory.whiskerLeft G₁ base) : Hom psi phi :=
  ⟨⟨left, right, base⟩, leftNaturality, rightNaturality⟩

/-- The component of a based cospan modification at the left endpoint. -/
def left (alpha : Hom psi phi) : psi.left ⟶ phi.left :=
  alpha.val.1

/-- The component of a based cospan modification at the right endpoint. -/
def right (alpha : Hom psi phi) : psi.right ⟶ phi.right :=
  alpha.val.2.1

/-- The component of a based cospan modification at the common target. -/
def base (alpha : Hom psi phi) : psi.base ⟶ phi.base :=
  alpha.val.2.2

/-- The left components of a based cospan modification satisfy the naturality equation. -/
theorem leftNaturality (alpha : Hom psi phi) :
    BasedCategory.whiskerRight alpha.left F₂ ≫ phi.leftIso.hom =
      psi.leftIso.hom ≫ BasedCategory.whiskerLeft F₁ alpha.base :=
  alpha.property.1

/-- The right components of a based cospan modification satisfy the naturality equation. -/
theorem rightNaturality (alpha : Hom psi phi) :
    BasedCategory.whiskerRight alpha.right G₂ ≫ phi.rightIso.hom =
      psi.rightIso.hom ≫ BasedCategory.whiskerLeft G₁ alpha.base :=
  alpha.property.2

/-- Identity components satisfy the left generating naturality square. -/
theorem id.leftNaturality (psi : BasedCospanTransform F₁ G₁ F₂ G₂) :
    BasedCategory.whiskerRight (𝟙 psi.left) F₂ ≫ psi.leftIso.hom =
      psi.leftIso.hom ≫ BasedCategory.whiskerLeft F₁ (𝟙 psi.base) := sorry

/-- Identity components satisfy the right generating naturality square. -/
theorem id.rightNaturality (psi : BasedCospanTransform F₁ G₁ F₂ G₂) :
    BasedCategory.whiskerRight (𝟙 psi.right) G₂ ≫ psi.rightIso.hom =
      psi.rightIso.hom ≫ BasedCategory.whiskerLeft G₁ (𝟙 psi.base) := sorry

/-- The identity modification of a based cospan transformation. -/
def id (psi : BasedCospanTransform F₁ G₁ F₂ G₂) : Hom psi psi :=
  mk (𝟙 psi.left) (𝟙 psi.right) (𝟙 psi.base)
    (id.leftNaturality psi) (id.rightNaturality psi)

/-- Vertically composed components satisfy the left generating naturality square. -/
theorem comp.leftNaturality (alpha : Hom psi phi) (beta : Hom phi chi) :
    BasedCategory.whiskerRight (alpha.left ≫ beta.left) F₂ ≫ chi.leftIso.hom =
      psi.leftIso.hom ≫
        BasedCategory.whiskerLeft F₁ (alpha.base ≫ beta.base) := sorry

/-- Vertically composed components satisfy the right generating naturality square. -/
theorem comp.rightNaturality (alpha : Hom psi phi) (beta : Hom phi chi) :
    BasedCategory.whiskerRight (alpha.right ≫ beta.right) G₂ ≫ chi.rightIso.hom =
      psi.rightIso.hom ≫
        BasedCategory.whiskerLeft G₁ (alpha.base ≫ beta.base) := sorry

/-- Vertical composition of modifications of based cospan transformations. -/
def comp (alpha : Hom psi phi) (beta : Hom phi chi) : Hom psi chi :=
  mk (alpha.left ≫ beta.left) (alpha.right ≫ beta.right) (alpha.base ≫ beta.base)
    (comp.leftNaturality alpha beta) (comp.rightNaturality alpha beta)

/-- A modification of based cospan transformations is determined by its three vertex
components. -/
@[ext]
theorem ext (alpha beta : Hom psi phi)
    (leftEq : alpha.left = beta.left) (rightEq : alpha.right = beta.right)
    (baseEq : alpha.base = beta.base) : alpha = beta := sorry

/-- The left component of an identity modification is an identity. -/
@[simp]
theorem id.left (psi : BasedCospanTransform F₁ G₁ F₂ G₂) :
    (id psi).left = 𝟙 psi.left := sorry

/-- The right component of an identity modification is an identity. -/
@[simp]
theorem id.right (psi : BasedCospanTransform F₁ G₁ F₂ G₂) :
    (id psi).right = 𝟙 psi.right := sorry

/-- The common-target component of an identity modification is an identity. -/
@[simp]
theorem id.base (psi : BasedCospanTransform F₁ G₁ F₂ G₂) :
    (id psi).base = 𝟙 psi.base := sorry

/-- The left component of a composite modification is the composite of its left components. -/
@[simp]
theorem comp.left (alpha : Hom psi phi) (beta : Hom phi chi) :
    (comp alpha beta).left = alpha.left ≫ beta.left := sorry

/-- The right component of a composite modification is the composite of its right components. -/
@[simp]
theorem comp.right (alpha : Hom psi phi) (beta : Hom phi chi) :
    (comp alpha beta).right = alpha.right ≫ beta.right := sorry

/-- The common-target component of a composite modification is the composite of its base
components. -/
@[simp]
theorem comp.base (alpha : Hom psi phi) (beta : Hom phi chi) :
    (comp alpha beta).base = alpha.base ≫ beta.base := sorry

/-- Identity is a left unit for vertical composition of based cospan modifications. -/
theorem id_comp (alpha : Hom psi phi) : comp (id psi) alpha = alpha := sorry

/-- Identity is a right unit for vertical composition of based cospan modifications. -/
theorem comp_id (alpha : Hom psi phi) : comp alpha (id phi) = alpha := sorry

/-- Vertical composition of based cospan modifications is associative. -/
theorem assoc {omega : BasedCospanTransform F₁ G₁ F₂ G₂}
    (alpha : Hom psi phi) (beta : Hom phi chi) (gamma : Hom chi omega) :
    comp (comp alpha beta) gamma = comp alpha (comp beta gamma) := sorry

end Hom

/-- For fixed source and target based cospans, transformations and modifications form a
category. -/
instance category : Category (BasedCospanTransform F₁ G₁ F₂ G₂) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- Evaluation of a based cospan transformation at the left endpoint. -/
def leftFunctor :
    BasedCospanTransform F₁ G₁ F₂ G₂ ⥤ (X₁ ⥤ᵇ X₂) where
  obj := fun psi => psi.left
  map := fun alpha => alpha.left
  map_id := Hom.id.left
  map_comp := Hom.comp.left

/-- Evaluation of a based cospan transformation at the right endpoint. -/
def rightFunctor :
    BasedCospanTransform F₁ G₁ F₂ G₂ ⥤ (Y₁ ⥤ᵇ Y₂) where
  obj := fun psi => psi.right
  map := fun alpha => alpha.right
  map_id := Hom.id.right
  map_comp := Hom.comp.right

/-- Evaluation of a based cospan transformation at the common target. -/
def baseFunctor :
    BasedCospanTransform F₁ G₁ F₂ G₂ ⥤ (S₁ ⥤ᵇ S₂) where
  obj := fun psi => psi.base
  map := fun alpha => alpha.base
  map_id := Hom.id.base
  map_comp := Hom.comp.base

end BasedCospanTransform

end CategoryTheory
