/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.ObjectProperty.Equivalence

/-!
# Congruence API for object properties of locally induced two-fibre products

The apex is invariant, for every equivalence-closed object property, under replacing either or
both cospan legs by isomorphic morphisms.
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
/-- Replacing both parallel selected cospan legs by isomorphic legs preserves every
equivalence-closed object property of their locally induced two-fibre-product apex. -/
theorem congr_iff
    {X Y S : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    {F F' : X ⟶ S} {G G' : Y ⟶ S}
    (α : F ≅ F') (β : G ≅ G')
    (R : ObjectProperty
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q))
    [R.IsClosedUnderEquivalences] :
    R (apex F G) ↔ R (apex F' G') := sorry
/- Proof strategy: specialize `congrCospan_iff` to identity equivalences at all
three vertices and the symmetries of `α` and `β`, inserting the canonical unitors. -/

include projections isoClosed detected in
/-- Replacing only the left selected cospan leg by an isomorphic leg preserves every
equivalence-closed object property of the locally induced two-fibre-product apex. -/
theorem congrLeft_iff
    {X Y S : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    {F F' : X ⟶ S} (G : Y ⟶ S) (α : F ≅ F')
    (R : ObjectProperty
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q))
    [R.IsClosedUnderEquivalences] :
    R (apex F G) ↔ R (apex F' G) := sorry
/- Proof strategy: specialize `congr_iff` with `α` and the identity isomorphism
of `G`. -/

include projections isoClosed detected in
/-- Replacing only the right selected cospan leg by an isomorphic leg preserves every
equivalence-closed object property of the locally induced two-fibre-product apex. -/
theorem congrRight_iff
    {X Y S : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    (F : X ⟶ S) {G G' : Y ⟶ S} (β : G ≅ G')
    (R : ObjectProperty
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q))
    [R.IsClosedUnderEquivalences] :
    R (apex F G) ↔ R (apex F G') := sorry
/- Proof strategy: specialize `congr_iff` with the identity isomorphism of `F`
and `β`. -/

end ObjectProperty

end TwoFibreProduct
end LocallyInduced

end CategoryTheory
