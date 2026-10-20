/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Bilimit
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.HomProperty

/-!
# Hom-property transport for explicit two-fibre products

Base-change stability lemmas for the two projections of the chosen bilimit cone.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

universe u v w vB

namespace CategoryTheory

open BasedCategory Bicategory ObjectProperty
open scoped Bicategory
open scoped Pseudofunctor.StrongTrans

variable {C : Type u} [Category.{v} C]

namespace TwoFibreProduct

variable
  {P : ObjectProperty
    (BasedCategory.{max v vB, max w (max u (max v vB))} C)}
variable [BasedCategory.PseudoPullback.ObjectProperty.IsClosedUnder P]
variable {X Y S : P.FullSubbicategory}

/-- The first projection of the explicit two-fibre product inherits a stable hom property from
the right cospan leg.

The fixed-leg hypothesis is intentional: it supports applications which only know stability
along `F`, while global `IsStableUnderBaseChange` instances are converted to this hypothesis
automatically. -/
theorem _root_.CategoryTheory.Bicategory.HomProperty.twoFibreProduct_fst
    (Q : Bicategory.HomProperty (fun X : P.FullSubbicategory ↦ X))
    (F : X ⟶ S) (G : Y ⟶ S)
    [Q.IsStableUnderBaseChangeAlong F] (hG : Q Y S G) :
    Q (apex F G) X (fst F G) := sorry
/- Proof strategy: apply `Q.pseudoPullback_fst` to `cone F G`, use `cone.isBilimit`, and simplify
the cone apex and first projection with `cone.pt` and `cone.fst`. -/

/-- The second projection of the explicit two-fibre product inherits a stable hom property from
the left cospan leg. -/
theorem _root_.CategoryTheory.Bicategory.HomProperty.twoFibreProduct_snd
    (Q : Bicategory.HomProperty (fun X : P.FullSubbicategory ↦ X))
    (F : X ⟶ S) (G : Y ⟶ S)
    [Q.IsStableUnderBaseChangeAlong G] (hF : Q X S F) :
    Q (apex F G) Y (snd F G) := sorry
/- Proof strategy: apply `Q.pseudoPullback_snd` to `cone F G`, use `cone.isBilimit`, and simplify
the cone apex and second projection with `cone.pt` and `cone.snd`. -/

end TwoFibreProduct

end CategoryTheory
