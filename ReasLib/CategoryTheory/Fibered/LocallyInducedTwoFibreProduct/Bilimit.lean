/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Basic
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# Bilimits of locally induced two-fibre products

This leaf provides the typeclass instance witnessing that the explicit selected cone is a
bilimit under projection detection.
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
variable {X Y S : Bicategory.LocallyInducedBicategory
  (BasedCategory.{max v vB, max w (max u (max v vB))} C) (fun X : P.FullSubbicategory ↦ X.1) Q}
variable [Projections.Has (P := P) (Q := Q)]

/-- Forgetting the selected data from the explicit locally induced cone yields an ordinary
pseudo-pullback bilimit without any detection or isomorphism-closure hypothesis on `Q`. -/
instance cone.forget.isBilimit (F : X ⟶ S) (G : Y ⟶ S) :
    (cone.forget F G).IsBilimit := sorry

/-- The explicit locally induced cone is a bilimit whenever the selected hom property is
detected by its projections. -/
@[stacks 02XQ "locally induced two-fibre products are bilimits"]
instance cone.isBilimit
    [Q.IsClosedUnderIsomorphisms]
    [Projections.IsDetected (P := P) (Q := Q)]
    (F : X ⟶ S) (G : Y ⟶ S) :
    (cone F G).IsBilimit := sorry
/- Proof strategy: apply
`Bicategory.PseudoPullbackCone.forgetLocallyInduced.isBilimit`. The forgotten cone is the
explicit `BasedCategory.PseudoPullback.cone`, and the detection class supplies the final
hom-membership implication. -/

end TwoFibreProduct
end LocallyInduced

end CategoryTheory
