/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Equivalence.ObjectProperty
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Pseudofunctor.Projections

/-!
# Equivalence transport for object properties of locally induced two-fibre products

These are the primary transport lemmas: first for equivalences of bundled cospans, then for
componentwise equivalent cospans.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory ObjectProperty
open scoped Bicategory BasedFunctor

variable {C : Type u} [Category.{v} C]

namespace LocallyInduced
namespace TwoFibreProduct

variable {P : ObjectProperty (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable {Q : Bicategory.HomProperty (fun X : P.FullSubbicategory ↦ X.1)}
variable [Q.IsMultiplicative]
variable [BasedCategory.PseudoPullback.HomProperty.IsClosedUnder Q]
variable [projections : Projections.Has (P := P) (Q := Q)]
variable [isoClosed : Q.IsClosedUnderIsomorphisms]
variable [detected : Projections.IsDetected (P := P) (Q := Q)]

namespace ObjectProperty

include projections isoClosed detected in
/-- Equivalent bundled selected cospans have locally induced two-fibre-product apices
satisfying exactly the same equivalence-closed object properties. -/
theorem cospanEquivalence_iff
    {S T : Bicategory.Cospan
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q)}
    (e : S ≌ T)
    (R : ObjectProperty
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q))
    [R.IsClosedUnderEquivalences] :
    R (apex S.fst S.snd) ↔ R (apex T.fst T.snd) := sorry
/- Proof strategy: apply `ObjectProperty.prop_iff_of_equivalence R` to
`pseudofunctor.mapEquivalence e`. -/

include projections isoClosed detected in
/-- Componentwise equivalent selected cospans have locally induced two-fibre-product apices
satisfying exactly the same equivalence-closed object properties. -/
theorem congrCospan_iff
    {X₁ Y₁ S₁ X₂ Y₂ S₂ : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    {F₁ : X₁ ⟶ S₁} {G₁ : Y₁ ⟶ S₁}
    {F₂ : X₂ ⟶ S₂} {G₂ : Y₂ ⟶ S₂}
    (eX : X₁ ≌ X₂) (eY : Y₁ ≌ Y₂) (eS : S₁ ≌ S₂)
    (α : eX.hom ≫ F₂ ≅ F₁ ≫ eS.hom)
    (β : eY.hom ≫ G₂ ≅ G₁ ≫ eS.hom)
    (R : ObjectProperty
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q))
    [R.IsClosedUnderEquivalences] :
    R (apex F₁ G₁) ↔ R (apex F₂ G₂) := sorry
/- Proof strategy: construct the bundled cospan equivalence with
`Bicategory.Cospan.equivalenceMk eX eY eS α β`, then apply
`cospanEquivalence_iff`. -/

end ObjectProperty

end TwoFibreProduct
end LocallyInduced

end CategoryTheory
