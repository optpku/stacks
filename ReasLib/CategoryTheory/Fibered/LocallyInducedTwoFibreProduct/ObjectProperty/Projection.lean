/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Equivalence.ObjectProperty
public import ReasLib.CategoryTheory.Fibered.LocallyInducedTwoFibreProduct.Bilimit

/-!
# Projection-pasting transport for locally induced two-fibre-product object properties

These are the reassociation-facing property transport lemmas for iterated locally induced
two-fibre products.
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
/-- Pulling back a first projection and reassociating locally induced two-fibre products
preserves every equivalence-closed object property. -/
theorem leftProjection_iff
    {A' A B T : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    (K : A' ⟶ A) (F : A ⟶ T) (G : B ⟶ T)
    (R : ObjectProperty
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q))
    [R.IsClosedUnderEquivalences] :
    R (apex K (fst F G)) ↔ R (apex (K ≫ F) G) := sorry
/- Proof strategy: paste the canonical bilimit cones for the two iterated pseudopullbacks,
compare their apices by bilimit uniqueness, and transport `R` across the resulting
equivalence. -/

include projections isoClosed detected in
/-- Pulling back a second projection and reassociating locally induced two-fibre products
preserves every equivalence-closed object property. -/
theorem rightProjection_iff
    {A B' B T : Bicategory.LocallyInducedBicategory
      (BasedCategory.{max v vB, max w (max u (max v vB))} C)
      (fun X : P.FullSubbicategory ↦ X.1) Q}
    (F : A ⟶ T) (G : B ⟶ T) (K : B' ⟶ B)
    (R : ObjectProperty
      (Bicategory.LocallyInducedBicategory
        (BasedCategory.{max v vB, max w (max u (max v vB))} C)
        (fun X : P.FullSubbicategory ↦ X.1) Q))
    [R.IsClosedUnderEquivalences] :
    R (apex (snd F G) K) ↔ R (apex F (K ≫ G)) := sorry
/- Proof strategy: derive this from `leftProjection_iff` by swapping the inner
and outer cospans, or use the symmetric bilimit-pasting argument. -/

end ObjectProperty

end TwoFibreProduct
end LocallyInduced

end CategoryTheory
