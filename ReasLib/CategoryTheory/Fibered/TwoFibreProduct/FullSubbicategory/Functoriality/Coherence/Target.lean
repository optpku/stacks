module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Projections
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.NatTrans.Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Target comparison for full-subbicategory two-fibre-product maps

The target square and its pasting, direct, inverse, and `2`-naturality APIs.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory Bicategory ObjectProperty
open scoped Bicategory Pseudofunctor.StrongTrans
  CategoryTheory.Bicategory.CospanTransform

variable {C : Type u} [Category.{v} C]

namespace TwoFibreProduct

variable
  {P : ObjectProperty
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable [BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder P]
variable {X₁ Y₁ S₁ X₂ Y₂ S₂ : P.FullSubbicategory}
variable {F₁ : X₁ ⟶ S₁} {G₁ : Y₁ ⟶ S₁}
variable {F₂ : X₂ ⟶ S₂} {G₂ : Y₂ ⟶ S₂}
variable {psi phi : CospanTransform F₁ G₁ F₂ G₂}

/-- The target comparison whiskered by the induced map of explicit two-fibre products. -/
@[stacks 0040 "target comparison for a full-subbicategory two-fibre-product map"]
noncomputable def map.comparisonIso
    (psi : CospanTransform F₁ G₁ F₂ G₂) :
    (map psi ≫ fst F₂ G₂) ≫ F₂ ≅ (map psi ≫ snd F₂ G₂) ≫ G₂ :=
  (α_ (map psi) (fst F₂ G₂) F₂) ≪≫
    whiskerLeftIso (map psi)
        (_root_.CategoryTheory.TwoFibreProduct.comparisonIso F₂ G₂) ≪≫
      (α_ (map psi) (snd F₂ G₂) G₂).symm

/-- Forgetting the forward target comparison recovers the explicit based pseudo-pullback
target comparison. -/
@[simp]
theorem map.comparisonIso.hom
    (psi : CospanTransform F₁ G₁ F₂ G₂) :
    (map.comparisonIso psi).hom.hom =
      (BasedCategory.PseudoPullback.map.comparisonIso
        (CospanTransform.forget psi)).hom := sorry

/-- Forgetting the inverse target comparison recovers the inverse explicit based
pseudo-pullback target comparison. -/
@[simp]
theorem map.comparisonIso.inv
    (psi : CospanTransform F₁ G₁ F₂ G₂) :
    (map.comparisonIso psi).inv.hom =
      (BasedCategory.PseudoPullback.map.comparisonIso
        (CospanTransform.forget psi)).inv := sorry

/-- Naturality of the two-fibre-product comparison under a cospan transformation, expressed as
the symmetric boundary pasting through the two projection comparisons. -/
theorem map.comparisonIso.equation
    (psi : CospanTransform F₁ G₁ F₂ G₂) :
    map.comparisonIso psi =
      whiskerRightIso (map.fstIso psi) F₂ ≪≫
        (α_ (fst F₁ G₁) psi.left F₂) ≪≫
          whiskerLeftIso (fst F₁ G₁) psi.leftIso ≪≫
            (α_ (fst F₁ G₁) F₁ psi.base).symm ≪≫
              whiskerRightIso
                  (_root_.CategoryTheory.TwoFibreProduct.comparisonIso F₁ G₁) psi.base ≪≫
                (α_ (snd F₁ G₁) G₁ psi.base) ≪≫
                  whiskerLeftIso (snd F₁ G₁) psi.rightIso.symm ≪≫
                    (α_ (snd F₁ G₁) psi.right G₂).symm ≪≫
                      whiskerRightIso (map.sndIso psi).symm G₂ := sorry

/-- The target comparison is `2`-natural in modifications of full-subbicategory cospan
transformations. -/
theorem map.comparisonIso.naturality
    (Gamma : Pseudofunctor.StrongTrans.Hom psi phi) :
    ((map₂ Gamma ▷ fst F₂ G₂) ▷ F₂) ≫ (map.comparisonIso phi).hom =
      (map.comparisonIso psi).hom ≫
        ((map₂ Gamma ▷ snd F₂ G₂) ▷ G₂) := sorry

/-- The inverse target comparison is `2`-natural in modifications of full-subbicategory cospan
transformations. -/
theorem map.comparisonIso.invNaturality
    (Gamma : Pseudofunctor.StrongTrans.Hom psi phi) :
    (map.comparisonIso psi).inv ≫
        ((map₂ Gamma ▷ fst F₂ G₂) ▷ F₂) =
      ((map₂ Gamma ▷ snd F₂ G₂) ▷ G₂) ≫
        (map.comparisonIso phi).inv := sorry

end TwoFibreProduct

end CategoryTheory
