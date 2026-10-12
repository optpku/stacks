/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Functoriality.Map.Construction
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.Comparison.Identity
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Functoriality.NatTrans.HomFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity comparison for full-subbicategory two-fibre-product maps

The canonical isomorphism comparing the map of an identity cospan transformation with the
identity of the selected two-fibre-product apex.
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
variable {X₁ Y₁ S₁ : P.FullSubbicategory}

/-- Canonical componentwise isomorphism for identity preservation. It combines the generic
forgetful identity comparison with the explicit pseudo-pullback identity coherence. -/
@[stacks 0040 "identity comparison for full-subbicategory two-fibre-product maps"]
noncomputable def map.idIso (F : X₁ ⟶ S₁) (G : Y₁ ⟶ S₁) :
    map (CospanTransform.id F G) ≅ 𝟙 (apex F G) :=
  Bicategory.InducedBicategory.isoMk
    (BasedCategory.PseudoPullback.map.iso
        (CospanTransform.forget.idIso F G) ≪≫
      BasedCategory.PseudoPullback.map.idIso F.hom G.hom)

/-- Forgetting the forward identity comparison recovers the composite of the generic
forgetful comparison with the explicit pseudo-pullback identity coherence. -/
@[simp]
theorem map.idIso.hom (F : X₁ ⟶ S₁) (G : Y₁ ⟶ S₁) :
    (map.idIso F G).hom.hom =
      (BasedCategory.PseudoPullback.map.iso
          (CospanTransform.forget.idIso F G) ≪≫
        BasedCategory.PseudoPullback.map.idIso F.hom G.hom).hom := sorry

/-- Forgetting the inverse identity comparison recovers the inverse composite of the generic
forgetful comparison with the explicit pseudo-pullback identity coherence. -/
@[simp]
theorem map.idIso.inv (F : X₁ ⟶ S₁) (G : Y₁ ⟶ S₁) :
    (map.idIso F G).inv.hom =
      (BasedCategory.PseudoPullback.map.iso
          (CospanTransform.forget.idIso F G) ≪≫
        BasedCategory.PseudoPullback.map.idIso F.hom G.hom).inv := sorry

end TwoFibreProduct

end CategoryTheory
