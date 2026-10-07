module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Whiskering

/-!
# Cospan transformations of based categories

This file defines universe-polymorphic transformations between cospans in `Cat/C`, together
with their identity and vertical composition operations.
-/

@[expose] public section

namespace CategoryTheory

open BasedFunctor

universe u v
universe uX₁ vX₁ uY₁ vY₁ uS₁ vS₁
universe uX₂ vX₂ uY₂ vY₂ uS₂ vS₂
universe uX₃ vX₃ uY₃ vY₃ uS₃ vS₃

variable {C : Type u} [Category.{v} C]
variable {X₁ : BasedCategory.{vX₁, uX₁} C}
variable {Y₁ : BasedCategory.{vY₁, uY₁} C}
variable {S₁ : BasedCategory.{vS₁, uS₁} C}
variable {X₂ : BasedCategory.{vX₂, uX₂} C}
variable {Y₂ : BasedCategory.{vY₂, uY₂} C}
variable {S₂ : BasedCategory.{vS₂, uS₂} C}
variable {X₃ : BasedCategory.{vX₃, uX₃} C}
variable {Y₃ : BasedCategory.{vY₃, uY₃} C}
variable {S₃ : BasedCategory.{vS₃, uS₃} C}

/-- A transformation between two cospans of categories over a common base.

The three component functors commute strictly with the projections to `C`; the two comparison
isomorphisms express pseudonaturality along the cospan legs. Source and target endpoint
categories are universe-independent. -/
structure BasedCospanTransform
    (F₁ : X₁ ⥤ᵇ S₁) (G₁ : Y₁ ⥤ᵇ S₁)
    (F₂ : X₂ ⥤ᵇ S₂) (G₂ : Y₂ ⥤ᵇ S₂) where
  /-- The based functor on the left endpoint. -/
  left : X₁ ⥤ᵇ X₂
  /-- The based functor on the right endpoint. -/
  right : Y₁ ⥤ᵇ Y₂
  /-- The based functor on the common target. -/
  base : S₁ ⥤ᵇ S₂
  /-- The comparison from the transformed target left leg to the source left leg followed by
  the common-target functor. -/
  leftIso : left ⋙ F₂ ≅ F₁ ⋙ base
  /-- The analogous comparison on the right leg. -/
  rightIso : right ⋙ G₂ ≅ G₁ ⋙ base

namespace BasedCospanTransform

variable {F₁ : X₁ ⥤ᵇ S₁} {G₁ : Y₁ ⥤ᵇ S₁}
variable {F₂ : X₂ ⥤ᵇ S₂} {G₂ : Y₂ ⥤ᵇ S₂}
variable {F₃ : X₃ ⥤ᵇ S₃} {G₃ : Y₃ ⥤ᵇ S₃}

/-- The identity transformation of a based cospan. -/
def id (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) :
    BasedCospanTransform F G F G where
  left := 𝟙 X₁
  right := 𝟙 Y₁
  base := 𝟙 S₁
  leftIso := BasedNatIso.id F
  rightIso := BasedNatIso.id G

/-- The left component of the identity based cospan transformation is the identity based
functor. -/
@[simp]
theorem id.left (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) :
    (id F G).left = 𝟙 X₁ := sorry

/-- The right component of the identity based cospan transformation is the identity based
functor. -/
@[simp]
theorem id.right (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) :
    (id F G).right = 𝟙 Y₁ := sorry

/-- The common-target component of the identity based cospan transformation is the identity
based functor. -/
@[simp]
theorem id.base (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) :
    (id F G).base = 𝟙 S₁ := sorry

/-- The left comparison of the identity based cospan transformation is the canonical identity
comparison. -/
@[simp]
theorem id.leftIso (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) :
    (id F G).leftIso = BasedNatIso.id F := sorry

/-- The right comparison of the identity based cospan transformation is the canonical identity
comparison. -/
@[simp]
theorem id.rightIso (F : X₁ ⥤ᵇ S₁) (G : Y₁ ⥤ᵇ S₁) :
    (id F G).rightIso = BasedNatIso.id G := sorry

/-- Vertical composition of universe-polymorphic based cospan transformations. -/
def comp
    (psi : BasedCospanTransform F₁ G₁ F₂ G₂)
    (phi : BasedCospanTransform F₂ G₂ F₃ G₃) :
    BasedCospanTransform F₁ G₁ F₃ G₃ where
  left := psi.left ⋙ phi.left
  right := psi.right ⋙ phi.right
  base := psi.base ⋙ phi.base
  leftIso :=
    BasedNatIso.whiskerLeft psi.left phi.leftIso ≪≫
      BasedNatIso.whiskerRight psi.leftIso phi.base
  rightIso :=
    BasedNatIso.whiskerLeft psi.right phi.rightIso ≪≫
      BasedNatIso.whiskerRight psi.rightIso phi.base

/-- The left component of a composite based cospan transformation is the composite of the left
components. -/
@[simp]
theorem comp.left
    (psi : BasedCospanTransform F₁ G₁ F₂ G₂)
    (phi : BasedCospanTransform F₂ G₂ F₃ G₃) :
    (comp psi phi).left = psi.left ⋙ phi.left := sorry

/-- The right component of a composite based cospan transformation is the composite of the
right components. -/
@[simp]
theorem comp.right
    (psi : BasedCospanTransform F₁ G₁ F₂ G₂)
    (phi : BasedCospanTransform F₂ G₂ F₃ G₃) :
    (comp psi phi).right = psi.right ⋙ phi.right := sorry

/-- The common-target component of a composite based cospan transformation is the composite of
the common-target components. -/
@[simp]
theorem comp.base
    (psi : BasedCospanTransform F₁ G₁ F₂ G₂)
    (phi : BasedCospanTransform F₂ G₂ F₃ G₃) :
    (comp psi phi).base = psi.base ⋙ phi.base := sorry

/-- The left comparison of a composite based cospan transformation is obtained by whiskering
and composing the two left comparisons. -/
@[simp]
theorem comp.leftIso
    (psi : BasedCospanTransform F₁ G₁ F₂ G₂)
    (phi : BasedCospanTransform F₂ G₂ F₃ G₃) :
    (comp psi phi).leftIso =
      BasedNatIso.whiskerLeft psi.left phi.leftIso ≪≫
        BasedNatIso.whiskerRight psi.leftIso phi.base := sorry

/-- The right comparison of a composite based cospan transformation is obtained by whiskering
and composing the two right comparisons. -/
@[simp]
theorem comp.rightIso
    (psi : BasedCospanTransform F₁ G₁ F₂ G₂)
    (phi : BasedCospanTransform F₂ G₂ F₃ G₃) :
    (comp psi phi).rightIso =
      BasedNatIso.whiskerLeft psi.right phi.rightIso ≪≫
        BasedNatIso.whiskerRight psi.rightIso phi.base := sorry

end BasedCospanTransform

end CategoryTheory
