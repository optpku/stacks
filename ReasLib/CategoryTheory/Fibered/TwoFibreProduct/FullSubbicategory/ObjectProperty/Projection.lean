/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Equivalence.ObjectProperty
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit

/-!
# Projection reassociation for two-fibre-product object properties

These bilimit-level statements transport equivalence-closed properties across iterated
two-fibre-product presentations involving a projection.
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

/-- Pulling back a first projection and then reassociating the two-fibre product preserves every
equivalence-closed object property. -/
theorem leftProjection_iff
    {A' A B T : P.FullSubbicategory}
    (K : A' ⟶ A) (F : A ⟶ T) (G : B ⟶ T)
    (R : ObjectProperty P.FullSubbicategory) [R.IsClosedUnderEquivalences] :
    R (apex K (fst F G)) ↔ R (apex (K ≫ F) G) := sorry

/-- Pulling back a second projection and then reassociating the two-fibre product preserves every
equivalence-closed object property. -/
theorem rightProjection_iff
    {A B' B T : P.FullSubbicategory}
    (F : A ⟶ T) (G : B ⟶ T) (K : B' ⟶ B)
    (R : ObjectProperty P.FullSubbicategory) [R.IsClosedUnderEquivalences] :
    R (apex (snd F G) K) ↔ R (apex F (K ≫ G)) := sorry

end ObjectProperty

end TwoFibreProduct

end CategoryTheory
