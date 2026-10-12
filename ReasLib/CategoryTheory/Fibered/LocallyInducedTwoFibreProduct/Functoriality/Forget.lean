/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Cospan.Bicategorical
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Category
public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Map.Modification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Forgetful cospan transformations for locally induced two-fibre products

This leaf translates selected cospan transformations and modifications to the ambient based
cospan language.  The induced pseudo-pullback maps live in `Functoriality.Map`.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory ObjectProperty
open scoped Bicategory BasedFunctor Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

variable {C : Type u} [Category.{v} C]

namespace LocallyInduced
namespace TwoFibreProduct

variable {P : ObjectProperty (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable {Q : Bicategory.HomProperty (fun X : P.FullSubbicategory ↦ X.1)}
variable [Q.IsMultiplicative]
variable {X₁ Y₁ S₁ X₂ Y₂ S₂ : Bicategory.LocallyInducedBicategory
  (BasedCategory.{max v vB, max w (max u (max v vB))} C) (fun X : P.FullSubbicategory ↦ X.1) Q}
variable {F₁ : X₁ ⟶ S₁} {G₁ : Y₁ ⟶ S₁}
variable {F₂ : X₂ ⟶ S₂} {G₂ : Y₂ ⟶ S₂}
variable {ψ φ : Bicategory.CospanTransform
  (B := Bicategory.LocallyInducedBicategory
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)
    (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂}

/-- Forget a cospan transformation in the locally induced bicategory to its transformation of
ambient based cospans. -/
@[stacks 0040 "forget a locally induced cospan transformation"]
noncomputable def CospanTransform.forget
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂) :
    BasedCospanTransform F₁.obj G₁.obj F₂.obj G₂.obj :=
  BasedCospanTransform.Bicategorical.obj
    (ψ.map
      (Bicategory.LocallyInducedBicategory.forget
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q).toPseudofunctor)

namespace CospanTransform.forget

/-- Forgetting an identity cospan transformation is canonically isomorphic to the identity
ordinary based cospan transformation. -/
@[stacks 0040 "forgetful identity comparison"]
noncomputable def idIso (F : X₁ ⟶ S₁) (G : Y₁ ⟶ S₁) :
    CospanTransform.forget (Bicategory.CospanTransform.id F G) ≅
      BasedCospanTransform.id F.obj G.obj :=
  BasedCospanTransform.Bicategorical.mapIdIso F G
    (Bicategory.LocallyInducedBicategory.forget
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q).toPseudofunctor

/-- Forgetting a composite cospan transformation is canonically isomorphic to the composite of
the two ordinary forgotten transformations. -/
@[stacks 0040 "forgetful composition comparison"]
noncomputable def compIso
    {X₃ Y₃ S₃ : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    {F₃ : X₃ ⟶ S₃} {G₃ : Y₃ ⟶ S₃}
    (ψ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₁ G₁ F₂ G₂)
    (φ : Bicategory.CospanTransform
      (B := Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q) F₂ G₂ F₃ G₃) :
    CospanTransform.forget (ψ.comp φ) ≅
      (CospanTransform.forget ψ).comp (CospanTransform.forget φ) :=
  BasedCospanTransform.Bicategorical.mapCompIso ψ φ
    (Bicategory.LocallyInducedBicategory.forget
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q).toPseudofunctor

end CospanTransform.forget

/-- Forgetting a selected cospan transformation retains its left endpoint morphism. -/
@[simp]
theorem CospanTransform.forget_left :
    (CospanTransform.forget ψ).left = ψ.left.obj := sorry

/-- Forgetting a selected cospan transformation retains its right endpoint morphism. -/
@[simp]
theorem CospanTransform.forget_right :
    (CospanTransform.forget ψ).right = ψ.right.obj := sorry

/-- Forgetting a selected cospan transformation retains its central morphism. -/
@[simp]
theorem CospanTransform.forget_base :
    (CospanTransform.forget ψ).base = ψ.base.obj := sorry

/-- Forgetting a selected cospan transformation transports its left comparison through the
forgetful pseudofunctor's composition and `2`-cell comparisons. -/
@[simp]
theorem CospanTransform.forget_leftIso :
    (CospanTransform.forget ψ).leftIso =
      (((Bicategory.LocallyInducedBicategory.forget
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)
          (fun X : P.FullSubbicategory ↦ X.1) Q).toPseudofunctor.mapComp
          ψ.left F₂).symm ≪≫
        (Bicategory.LocallyInducedBicategory.forget
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)
          (fun X : P.FullSubbicategory ↦ X.1) Q).toPseudofunctor.map₂Iso
          ψ.leftIso ≪≫
        (Bicategory.LocallyInducedBicategory.forget
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)
          (fun X : P.FullSubbicategory ↦ X.1) Q).toPseudofunctor.mapComp
          F₁ ψ.base) := sorry

/-- Forgetting a selected cospan transformation transports its right comparison through the
forgetful pseudofunctor's composition and `2`-cell comparisons. -/
@[simp]
theorem CospanTransform.forget_rightIso :
    (CospanTransform.forget ψ).rightIso =
      (((Bicategory.LocallyInducedBicategory.forget
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)
          (fun X : P.FullSubbicategory ↦ X.1) Q).toPseudofunctor.mapComp
          ψ.right G₂).symm ≪≫
        (Bicategory.LocallyInducedBicategory.forget
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)
          (fun X : P.FullSubbicategory ↦ X.1) Q).toPseudofunctor.map₂Iso
          ψ.rightIso ≪≫
        (Bicategory.LocallyInducedBicategory.forget
          (BasedCategory.{max v vB, max w (max u (max v vB))} C)
          (fun X : P.FullSubbicategory ↦ X.1) Q).toPseudofunctor.mapComp
          G₁ ψ.base) := sorry

/-- Forget a modification between selected cospan transformations to the corresponding
modification between ambient based cospans. -/
@[stacks 0040 "forget a locally induced cospan modification"]
noncomputable def CospanModification.forget
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    BasedCospanTransform.Hom
      (CospanTransform.forget ψ) (CospanTransform.forget φ) :=
  BasedCospanTransform.Bicategorical.map
    (Bicategory.CospanTransform.Hom.map Γ
      (Bicategory.LocallyInducedBicategory.forget
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q).toPseudofunctor)

/-- Forgetting a selected cospan modification retains its left endpoint cell. -/
@[simp]
theorem CospanModification.forget_left
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    (CospanModification.forget Γ).left =
      (Bicategory.CospanTransform.Hom.left Γ).hom := sorry

/-- Forgetting a selected cospan modification retains its right endpoint cell. -/
@[simp]
theorem CospanModification.forget_right
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    (CospanModification.forget Γ).right =
      (Bicategory.CospanTransform.Hom.right Γ).hom := sorry

/-- Forgetting a selected cospan modification retains its central cell. -/
@[simp]
theorem CospanModification.forget_base
    (Γ : Pseudofunctor.StrongTrans.Hom ψ φ) :
    (CospanModification.forget Γ).base =
      (Bicategory.CospanTransform.Hom.base Γ).hom := sorry

end TwoFibreProduct
end LocallyInduced
end CategoryTheory
