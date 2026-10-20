/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Graph
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Symmetry.Equivalence

/-!
# Identity and symmetry transport for two-fibre-product object properties
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

/-- An equivalence-closed object property holds on the two-fibre product of a morphism with the
target identity exactly when it holds on the morphism's source. -/
theorem rightIdentity_iff
    {X Y : P.FullSubbicategory} (F : X ⟶ Y)
    (R : ObjectProperty P.FullSubbicategory) [R.IsClosedUnderEquivalences] :
    R (apex F (𝟙 Y)) ↔ R X := sorry

/-- An equivalence-closed object property holds on the two-fibre product of an identity with a
morphism exactly when it holds on the morphism's source. -/
theorem leftIdentity_iff
    {X Y : P.FullSubbicategory} (F : X ⟶ Y)
    (R : ObjectProperty P.FullSubbicategory) [R.IsClosedUnderEquivalences] :
    R (apex (𝟙 Y) F) ↔ R X := sorry

/-- Exchanging the two legs of a two-fibre product preserves every equivalence-closed object
property. -/
theorem swap_iff
    {X Y S : P.FullSubbicategory} (F : X ⟶ S) (G : Y ⟶ S)
    (R : ObjectProperty P.FullSubbicategory) [R.IsClosedUnderEquivalences] :
    R (apex F G) ↔ R (apex G F) := sorry

end ObjectProperty

end TwoFibreProduct

end CategoryTheory
