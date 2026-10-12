/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.ObjectProperty.Equivalence
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Graph
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Symmetry.Equivalence

/-!
# Change-of-presentation API for locally induced two-fibre products

This layer specializes cospan-equivalence transport to changing an endpoint, the common base,
identity legs, and the ordering of the two legs.
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
variable [detected : Projections.IsDetected (P := P) (Q := Q)]

namespace ObjectProperty

section CospanEquivalence

variable [isoClosed : Q.IsClosedUnderIsomorphisms]

include projections isoClosed detected in
/-- Changing the left endpoint of a selected cospan by an equivalence preserves every
equivalence-closed object property of its locally induced two-fibre-product apex. -/
theorem changeLeft_iff
    {X X' Y S : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    {F : X ⟶ S} {F' : X' ⟶ S} (G : Y ⟶ S)
    (e : X ≌ X') (α : e.hom ≫ F' ≅ F)
    (R : ObjectProperty
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q))
    [R.IsClosedUnderEquivalences] :
    R (apex F G) ↔ R (apex F' G) := sorry
/- Proof strategy: specialize `congrCospan_iff` to `e`, identity equivalences on
`Y` and `S`, `α`, and the canonical unitor comparison for `G`. -/

include projections isoClosed detected in
/-- Changing the right endpoint of a selected cospan by an equivalence preserves every
equivalence-closed object property of its locally induced two-fibre-product apex. -/
theorem changeRight_iff
    {X Y Y' S : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    (F : X ⟶ S) {G : Y ⟶ S} {G' : Y' ⟶ S}
    (e : Y ≌ Y') (β : e.hom ≫ G' ≅ G)
    (R : ObjectProperty
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q))
    [R.IsClosedUnderEquivalences] :
    R (apex F G) ↔ R (apex F G') := sorry
/- Proof strategy: specialize `congrCospan_iff` to identity equivalences on `X`
and `S`, `e`, the canonical unitor comparison for `F`, and `β`. -/

include projections isoClosed detected in
/-- Changing the common target of a selected cospan by an equivalence, together with compatible
presentations of both legs, preserves every equivalence-closed object property of the locally
induced two-fibre-product apex. -/
theorem changeBase_iff
    {X Y S T : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    {F : X ⟶ S} {G : Y ⟶ S} {F' : X ⟶ T} {G' : Y ⟶ T}
    (e : S ≌ T) (α : F ≫ e.hom ≅ F') (β : G ≫ e.hom ≅ G')
    (R : ObjectProperty
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q))
    [R.IsClosedUnderEquivalences] :
    R (apex F G) ↔ R (apex F' G') := sorry
/- Proof strategy: specialize `congrCospan_iff` to identity endpoint
equivalences, `e`, and the symmetries of `α` and `β`, inserting the canonical unitors. -/

end CospanEquivalence

include projections detected in
/-- An equivalence-closed object property holds on the locally induced two-fibre product of a
selected morphism with the target identity exactly when it holds on the source. -/
theorem rightIdentity_iff
    {X Y : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    (F : X ⟶ Y)
    (R : ObjectProperty
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q))
    [R.IsClosedUnderEquivalences] :
    R (apex F (𝟙 Y)) ↔ R X := sorry
/- Proof strategy: transport `R` along `graph.equivalence F`, reversing the orientation of
`ObjectProperty.prop_iff_of_equivalence`. -/

include projections detected in
/-- An equivalence-closed object property holds on the locally induced two-fibre product of an
identity with a selected morphism exactly when it holds on the source. -/
theorem leftIdentity_iff
    {X Y : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    (F : X ⟶ Y)
    (R : ObjectProperty
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q))
    [R.IsClosedUnderEquivalences] :
    R (apex (𝟙 Y) F) ↔ R X := sorry
/- Proof strategy: first apply `swap_iff`, then `rightIdentity_iff`. -/

include projections detected in
/-- Exchanging the two legs of a selected cospan preserves every equivalence-closed object
property of its locally induced two-fibre-product apex. -/
theorem swap_iff
    {X Y S : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    (F : X ⟶ S) (G : Y ⟶ S)
    (R : ObjectProperty
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q))
    [R.IsClosedUnderEquivalences] :
    R (apex F G) ↔ R (apex G F) := sorry
/- Proof strategy: apply `ObjectProperty.prop_iff_of_equivalence R` to
`swap.equivalence F G`. -/

end ObjectProperty

end TwoFibreProduct
end LocallyInduced

end CategoryTheory
