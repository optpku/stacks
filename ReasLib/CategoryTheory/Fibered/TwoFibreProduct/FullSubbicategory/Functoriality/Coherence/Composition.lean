module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Construction
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.Comparison.Composition
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.NatTrans.HomFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition comparison for full-subbicategory two-fibre-product maps

The canonical isomorphism comparing the map of a composite cospan transformation with the
composite of the selected maps.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory Bicategory ObjectProperty
open scoped Bicategory CategoryTheory.Bicategory.CospanTransform

variable {C : Type u} [Category.{v} C]

namespace TwoFibreProduct

variable
  {P : ObjectProperty
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable [BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder P]
variable {X₁ Y₁ S₁ X₂ Y₂ S₂ : P.FullSubbicategory}
variable {F₁ : X₁ ⟶ S₁} {G₁ : Y₁ ⟶ S₁}
variable {F₂ : X₂ ⟶ S₂} {G₂ : Y₂ ⟶ S₂}

/-- Canonical componentwise isomorphism for composition preservation. It combines the generic
forgetful composition comparison with the explicit pseudo-pullback composition coherence. -/
@[stacks 0040 "composition comparison for full-subbicategory two-fibre-product maps"]
noncomputable def map.compIso
    {X₃ Y₃ S₃ : P.FullSubbicategory}
    {F₃ : X₃ ⟶ S₃} {G₃ : Y₃ ⟶ S₃}
    (psi : CospanTransform F₁ G₁ F₂ G₂)
    (phi : CospanTransform F₂ G₂ F₃ G₃) :
    map (psi.comp phi) ≅ map psi ≫ map phi :=
  Bicategory.InducedBicategory.isoMk
    (BasedCategory.PseudoPullback.map.iso
        (CospanTransform.forget.compIso psi phi) ≪≫
      BasedCategory.PseudoPullback.map.compIso
        (CospanTransform.forget psi) (CospanTransform.forget phi))

/-- Forgetting the forward composition comparison recovers the generic forgetful comparison
followed by the explicit pseudo-pullback composition coherence. -/
@[simp]
theorem map.compIso.hom
    {X₃ Y₃ S₃ : P.FullSubbicategory}
    {F₃ : X₃ ⟶ S₃} {G₃ : Y₃ ⟶ S₃}
    (psi : CospanTransform F₁ G₁ F₂ G₂)
    (phi : CospanTransform F₂ G₂ F₃ G₃) :
    (map.compIso psi phi).hom.hom =
      (BasedCategory.PseudoPullback.map.iso
          (CospanTransform.forget.compIso psi phi) ≪≫
        BasedCategory.PseudoPullback.map.compIso
          (CospanTransform.forget psi) (CospanTransform.forget phi)).hom := sorry

/-- Forgetting the inverse composition comparison recovers the inverse of the generic
forgetful comparison followed by the explicit pseudo-pullback composition coherence. -/
@[simp]
theorem map.compIso.inv
    {X₃ Y₃ S₃ : P.FullSubbicategory}
    {F₃ : X₃ ⟶ S₃} {G₃ : Y₃ ⟶ S₃}
    (psi : CospanTransform F₁ G₁ F₂ G₂)
    (phi : CospanTransform F₂ G₂ F₃ G₃) :
    (map.compIso psi phi).inv.hom =
      (BasedCategory.PseudoPullback.map.iso
          (CospanTransform.forget.compIso psi phi) ≪≫
        BasedCategory.PseudoPullback.map.compIso
          (CospanTransform.forget psi) (CospanTransform.forget phi)).inv := sorry

end TwoFibreProduct

end CategoryTheory
