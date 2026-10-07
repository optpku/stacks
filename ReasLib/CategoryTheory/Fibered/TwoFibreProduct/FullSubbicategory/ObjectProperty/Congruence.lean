module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.ObjectProperty.Equivalence

/-!
# Congruence API for two-fibre-product object properties

These lemmas remove isomorphic changes of one or both cospan legs, including changes detected
after postcomposition by a bicategorical equivalence.
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

/-- Replacing both parallel cospan legs by isomorphic legs preserves every equivalence-closed
object property of their two-fibre-product apex. -/
theorem congr_iff
    {X Y S : P.FullSubbicategory}
    {F F' : X ⟶ S} {G G' : Y ⟶ S}
    (α : F ≅ F') (β : G ≅ G')
    (R : ObjectProperty P.FullSubbicategory) [R.IsClosedUnderEquivalences] :
    R (apex F G) ↔ R (apex F' G') := sorry

/-- Replacing only the left cospan leg by an isomorphic leg preserves every equivalence-closed
object property of the two-fibre-product apex. -/
theorem congrLeft_iff
    {X Y S : P.FullSubbicategory}
    {F F' : X ⟶ S} (G : Y ⟶ S) (α : F ≅ F')
    (R : ObjectProperty P.FullSubbicategory) [R.IsClosedUnderEquivalences] :
    R (apex F G) ↔ R (apex F' G) := sorry

/-- Replacing only the right cospan leg by an isomorphic leg preserves every equivalence-closed
object property of the two-fibre-product apex. -/
theorem congrRight_iff
    {X Y S : P.FullSubbicategory}
    (F : X ⟶ S) {G G' : Y ⟶ S} (β : G ≅ G')
    (R : ObjectProperty P.FullSubbicategory) [R.IsClosedUnderEquivalences] :
    R (apex F G) ↔ R (apex F G') := sorry

/-- If both pairs of cospan legs become isomorphic after postcomposition by a bicategorical
equivalence, then every equivalence-closed object property holds on their two-fibre-product
apices simultaneously. -/
theorem congrPostcomp_iff
    {X Y S T : P.FullSubbicategory}
    {F F' : X ⟶ S} {G G' : Y ⟶ S}
    (e : S ≌ T)
    (α : F ≫ e.hom ≅ F' ≫ e.hom)
    (β : G ≫ e.hom ≅ G' ≫ e.hom)
    (R : ObjectProperty P.FullSubbicategory) [R.IsClosedUnderEquivalences] :
    R (apex F G) ↔ R (apex F' G') := sorry

/-- If two left cospan legs become isomorphic after postcomposition by a bicategorical
equivalence, replacing one by the other preserves every equivalence-closed property of the
two-fibre-product apex. -/
theorem congrPostcompLeft_iff
    {X Y S T : P.FullSubbicategory}
    {F F' : X ⟶ S} (G : Y ⟶ S)
    (e : S ≌ T) (α : F ≫ e.hom ≅ F' ≫ e.hom)
    (R : ObjectProperty P.FullSubbicategory) [R.IsClosedUnderEquivalences] :
    R (apex F G) ↔ R (apex F' G) := sorry

/-- If two right cospan legs become isomorphic after postcomposition by a bicategorical
equivalence, replacing one by the other preserves every equivalence-closed property of the
two-fibre-product apex. -/
theorem congrPostcompRight_iff
    {X Y S T : P.FullSubbicategory}
    (F : X ⟶ S) {G G' : Y ⟶ S}
    (e : S ≌ T) (β : G ≫ e.hom ≅ G' ≫ e.hom)
    (R : ObjectProperty P.FullSubbicategory) [R.IsClosedUnderEquivalences] :
    R (apex F G) ↔ R (apex F G') := sorry

end ObjectProperty

end TwoFibreProduct

end CategoryTheory
