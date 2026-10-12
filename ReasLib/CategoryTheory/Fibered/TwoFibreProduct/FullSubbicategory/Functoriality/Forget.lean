/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Cospan.Bicategorical
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Map.Modification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Forgetting full-subbicategory cospan transformations

Computational bridges from selected cospan transformations and modifications to their based counterparts.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory Bicategory ObjectProperty
open scoped Bicategory
open scoped Pseudofunctor.StrongTrans
open scoped CategoryTheory.Bicategory.CospanTransform

variable {C : Type u} [Category.{v} C]

namespace TwoFibreProduct

variable
  {P : ObjectProperty
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable {X Y S : P.FullSubbicategory}

section Functoriality

variable {X₁ Y₁ S₁ X₂ Y₂ S₂ : P.FullSubbicategory}
variable {F₁ : X₁ ⟶ S₁} {G₁ : Y₁ ⟶ S₁}
variable {F₂ : X₂ ⟶ S₂} {G₂ : Y₂ ⟶ S₂}
variable {ψ φ χ : CospanTransform F₁ G₁ F₂ G₂}

/-- Forget a cospan transformation in the full subbicategory to the corresponding transformation
of ambient based cospans. -/
@[stacks 0040 "forget a full-subbicategory cospan transformation"]
noncomputable def CospanTransform.forget
    (ψ : CospanTransform F₁ G₁ F₂ G₂) :
    BasedCospanTransform F₁.hom G₁.hom F₂.hom G₂.hom :=
  BasedCospanTransform.Bicategorical.obj
    (ψ.map (ObjectProperty.FullSubbicategory.ι P).toPseudofunctor)

namespace CospanTransform.forget

/-- Forgetting an identity cospan transformation is canonically isomorphic to the identity
generic based cospan transformation. -/
@[stacks 0040 "forgetful identity comparison for a full-subbicategory cospan"]
noncomputable def idIso (F : X₁ ⟶ S₁) (G : Y₁ ⟶ S₁) :
    CospanTransform.forget (CospanTransform.id F G) ≅
      BasedCospanTransform.id F.hom G.hom :=
  BasedCospanTransform.Bicategorical.mapIdIso F G
    (ObjectProperty.FullSubbicategory.ι P).toPseudofunctor

/-- Forgetting a composite cospan transformation is canonically isomorphic to the composite
of the two generic forgotten transformations. -/
@[stacks 0040 "forgetful composition comparison for full-subbicategory cospans"]
noncomputable def compIso
    {X₃ Y₃ S₃ : P.FullSubbicategory}
    {F₃ : X₃ ⟶ S₃} {G₃ : Y₃ ⟶ S₃}
    (ψ : CospanTransform F₁ G₁ F₂ G₂)
    (φ : CospanTransform F₂ G₂ F₃ G₃) :
    CospanTransform.forget (ψ.comp φ) ≅
      (CospanTransform.forget ψ).comp (CospanTransform.forget φ) :=
  BasedCospanTransform.Bicategorical.mapCompIso ψ φ
    (ObjectProperty.FullSubbicategory.ι P).toPseudofunctor

end CospanTransform.forget

/-- Forgetting a cospan transformation retains its left endpoint morphism. -/
@[simp]
theorem CospanTransform.forget_left
    (ψ : CospanTransform F₁ G₁ F₂ G₂) :
    (CospanTransform.forget ψ).left = ψ.left.hom := sorry

/-- Forgetting a cospan transformation retains its right endpoint morphism. -/
@[simp]
theorem CospanTransform.forget_right
    (ψ : CospanTransform F₁ G₁ F₂ G₂) :
    (CospanTransform.forget ψ).right = ψ.right.hom := sorry

/-- Forgetting a cospan transformation retains its central morphism. -/
@[simp]
theorem CospanTransform.forget_base
    (ψ : CospanTransform F₁ G₁ F₂ G₂) :
    (CospanTransform.forget ψ).base = ψ.base.hom := sorry

/-- Forgetting a cospan transformation transports its left comparison through the inclusion
pseudofunctor's composition and `2`-cell comparisons. -/
@[simp]
theorem CospanTransform.forget_leftIso
    (ψ : CospanTransform F₁ G₁ F₂ G₂) :
    (CospanTransform.forget ψ).leftIso =
      (((ObjectProperty.FullSubbicategory.ι P).toPseudofunctor.mapComp
          ψ.left F₂).symm ≪≫
        (ObjectProperty.FullSubbicategory.ι P).toPseudofunctor.map₂Iso
          ψ.leftIso ≪≫
        (ObjectProperty.FullSubbicategory.ι P).toPseudofunctor.mapComp
          F₁ ψ.base) := sorry

/-- Forgetting a cospan transformation transports its right comparison through the inclusion
pseudofunctor's composition and `2`-cell comparisons. -/
@[simp]
theorem CospanTransform.forget_rightIso
    (ψ : CospanTransform F₁ G₁ F₂ G₂) :
    (CospanTransform.forget ψ).rightIso =
      (((ObjectProperty.FullSubbicategory.ι P).toPseudofunctor.mapComp
          ψ.right G₂).symm ≪≫
        (ObjectProperty.FullSubbicategory.ι P).toPseudofunctor.map₂Iso
          ψ.rightIso ≪≫
        (ObjectProperty.FullSubbicategory.ι P).toPseudofunctor.mapComp
          G₁ ψ.base) := sorry

/-- Forget a modification between cospan transformations in the full subbicategory to the
corresponding modification of ambient based cospans. -/
@[stacks 0040 "forget a full-subbicategory cospan modification"]
noncomputable def CospanModification.forget
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    BasedCospanTransform.Hom
      (CospanTransform.forget ψ) (CospanTransform.forget φ) :=
  BasedCospanTransform.Bicategorical.map
    (CospanTransform.Hom.map Γ
      (ObjectProperty.FullSubbicategory.ι P).toPseudofunctor)

/-- Forgetting a cospan modification retains its left endpoint cell. -/
@[simp]
theorem CospanModification.forget_left
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    (CospanModification.forget Γ).left =
      (CospanTransform.Hom.left Γ).hom := sorry

/-- Forgetting a cospan modification retains its right endpoint cell. -/
@[simp]
theorem CospanModification.forget_right
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    (CospanModification.forget Γ).right =
      (CospanTransform.Hom.right Γ).hom := sorry

/-- Forgetting a cospan modification retains its central cell. -/
@[simp]
theorem CospanModification.forget_base
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    (CospanModification.forget Γ).base =
      (CospanTransform.Hom.base Γ).hom := sorry

end Functoriality

end TwoFibreProduct

end CategoryTheory
