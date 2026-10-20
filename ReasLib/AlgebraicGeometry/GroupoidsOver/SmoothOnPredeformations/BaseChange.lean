/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.SmoothOnPredeformations
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback

/-!
# Base change of smoothness on predeformations

Smoothness on associated predeformations is stable under canonical
two-fibre-product base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Over a locally Noetherian scheme, the canonical second projection from a
two-fibre product is smooth on predeformations whenever the morphism being
base changed is smooth on predeformations. -/
@[stacks 07XV]
instance IsSmoothOnPredeformations.twoFibreProduct_snd
    {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsSmoothOnPredeformations f] :
    IsSmoothOnPredeformations (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
