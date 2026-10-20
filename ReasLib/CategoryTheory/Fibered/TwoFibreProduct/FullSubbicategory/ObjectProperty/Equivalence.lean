module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Pseudofunctor.Construction
public import ReasLib.CategoryTheory.Bicategory.Equivalence.ObjectProperty

/-!
# Object-property transport along cospan equivalences

This leaf contains the general equivalence-invariance API for explicit two-fibre-product
apices in a full subbicategory.
-/

@[expose] public section

universe u v w vB

namespace CategoryTheory

open BasedCategory Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace TwoFibreProduct

variable {P : ObjectProperty
  (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable [BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder P]

namespace ObjectProperty

/-- Equivalent bundled cospans have two-fibre-product apices satisfying exactly the same
equivalence-closed object properties. -/
theorem cospanEquivalence_iff
    {S T : Bicategory.Cospan P.FullSubbicategory}
    (e : S ≌ T)
    (R : ObjectProperty P.FullSubbicategory) [R.IsClosedUnderEquivalences] :
    R (apex S.fst S.snd) ↔ R (apex T.fst T.snd) := sorry

/-- Componentwise equivalent cospans have two-fibre-product apices satisfying exactly the same
equivalence-closed object properties. -/
theorem congrCospan_iff
    {X₁ Y₁ S₁ X₂ Y₂ S₂ : P.FullSubbicategory}
    {F₁ : X₁ ⟶ S₁} {G₁ : Y₁ ⟶ S₁}
    {F₂ : X₂ ⟶ S₂} {G₂ : Y₂ ⟶ S₂}
    (eX : X₁ ≌ X₂) (eY : Y₁ ≌ Y₂) (eS : S₁ ≌ S₂)
    (α : eX.hom ≫ F₂ ≅ F₁ ≫ eS.hom)
    (β : eY.hom ≫ G₂ ≅ G₁ ≫ eS.hom)
    (R : ObjectProperty P.FullSubbicategory) [R.IsClosedUnderEquivalences] :
    R (apex F₁ G₁) ↔ R (apex F₂ G₂) := sorry

/-- Changing the left endpoint of a cospan by an equivalence preserves every
equivalence-closed object property of its two-fibre-product apex. -/
theorem changeLeft_iff
    {X X' Y S : P.FullSubbicategory}
    {F : X ⟶ S} {F' : X' ⟶ S} (G : Y ⟶ S)
    (e : X ≌ X') (α : e.hom ≫ F' ≅ F)
    (R : ObjectProperty P.FullSubbicategory) [R.IsClosedUnderEquivalences] :
    R (apex F G) ↔ R (apex F' G) := sorry

/-- Changing the right endpoint of a cospan by an equivalence preserves every
equivalence-closed object property of its two-fibre-product apex. -/
theorem changeRight_iff
    {X Y Y' S : P.FullSubbicategory}
    (F : X ⟶ S) {G : Y ⟶ S} {G' : Y' ⟶ S}
    (e : Y ≌ Y') (β : e.hom ≫ G' ≅ G)
    (R : ObjectProperty P.FullSubbicategory) [R.IsClosedUnderEquivalences] :
    R (apex F G) ↔ R (apex F G') := sorry

/-- Changing the common target of a cospan by an equivalence, together with compatible
presentations of both legs, preserves every equivalence-closed object property of the
two-fibre-product apex. -/
theorem changeBase_iff
    {X Y S T : P.FullSubbicategory}
    {F : X ⟶ S} {G : Y ⟶ S} {F' : X ⟶ T} {G' : Y ⟶ T}
    (e : S ≌ T) (α : F ≫ e.hom ≅ F') (β : G ≫ e.hom ≅ G')
    (R : ObjectProperty P.FullSubbicategory) [R.IsClosedUnderEquivalences] :
    R (apex F G) ↔ R (apex F' G') := sorry

end ObjectProperty

end TwoFibreProduct

end CategoryTheory
