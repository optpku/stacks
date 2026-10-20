/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.SmoothOnPredeformations.BaseChange
import StacksCheckRecall

/-!
# Base change of smoothness on predeformations

Smoothness on associated predeformations is stable under 2-fibre-product
base change of 1-morphisms of categories fibred in groupoids over
`(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/- Lemma 98.13.5: if `S` is locally Noetherian and `f : X ⟶ Y`, `g : Z ⟶ Y`
are 1-morphisms of categories fibred in groupoids over `(Sch/S)_fppf`, and `f`
is smooth on predeformations, then so is the projection
`TwoFibreProduct.snd f g`. -/
@[stacks 07XV] #check
  (AlgebraicGeometry.Groupoids.Hom.IsSmoothOnPredeformations.twoFibreProduct_snd :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
      {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Z ⟶ Y)
      [IsSmoothOnPredeformations f],
      IsSmoothOnPredeformations (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))

end AlgebraicGeometry.Groupoids.Hom
