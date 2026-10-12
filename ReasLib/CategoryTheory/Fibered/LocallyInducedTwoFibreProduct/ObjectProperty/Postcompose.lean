/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.ObjectProperty.Congruence

/-!
# Postcomposition transport for locally induced two-fibre-product object properties

These lemmas reflect isomorphisms after postcomposition by a bicategorical equivalence before
transporting an equivalence-closed property of the apex.
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
/-- If both pairs of selected cospan legs become isomorphic after postcomposition by a
bicategorical equivalence, then every equivalence-closed object property holds on their locally
induced two-fibre-product apices simultaneously. -/
theorem congrPostcomp_iff
    {X Y S T : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    {F F' : X ⟶ S} {G G' : Y ⟶ S}
    (e : S ≌ T)
    (α : F ≫ e.hom ≅ F' ≫ e.hom)
    (β : G ≫ e.hom ≅ G' ≫ e.hom)
    (R : ObjectProperty
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q))
    [R.IsClosedUnderEquivalences] :
    R (apex F G) ↔ R (apex F' G') := sorry
/- Proof strategy: use `Bicategory.postcomp_isEquivalence` and
`Functor.FullyFaithful.preimageIso` to reflect `α` and `β`, then apply
`congr_iff`. -/

include projections isoClosed detected in
/-- If two left selected cospan legs become isomorphic after postcomposition by a
bicategorical equivalence, replacing one by the other preserves every equivalence-closed
property of the locally induced two-fibre-product apex. -/
theorem congrPostcompLeft_iff
    {X Y S T : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    {F F' : X ⟶ S} (G : Y ⟶ S)
    (e : S ≌ T) (α : F ≫ e.hom ≅ F' ≫ e.hom)
    (R : ObjectProperty
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q))
    [R.IsClosedUnderEquivalences] :
    R (apex F G) ↔ R (apex F' G) := sorry
/- Proof strategy: specialize `congrPostcomp_iff` with `α` and the identity
isomorphism of `G ≫ e.hom`. -/

include projections isoClosed detected in
/-- If two right selected cospan legs become isomorphic after postcomposition by a
bicategorical equivalence, replacing one by the other preserves every equivalence-closed
property of the locally induced two-fibre-product apex. -/
theorem congrPostcompRight_iff
    {X Y S T : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    (F : X ⟶ S) {G G' : Y ⟶ S}
    (e : S ≌ T) (β : G ≫ e.hom ≅ G' ≫ e.hom)
    (R : ObjectProperty
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q))
    [R.IsClosedUnderEquivalences] :
    R (apex F G) ↔ R (apex F G') := sorry
/- Proof strategy: specialize `congrPostcomp_iff` with the identity isomorphism
of `F ≫ e.hom` and `β`. -/

end ObjectProperty

end TwoFibreProduct
end LocallyInduced

end CategoryTheory
