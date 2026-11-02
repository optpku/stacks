/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.RimSchlessinger
public import ReasLib.CategoryTheory.Fibered.BasedCategory.InGroupoids.PseudoPullback
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic

/-!
# Two-fibre products and the Rim-Schlessinger condition

The Rim-Schlessinger condition is stable under canonical two-fibre products of
categories fibred in groupoids over an arbitrary scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}
variable {X Y Z : GroupoidsOver S}

/-- The canonical two-fibre product of a cospan of categories fibred in groupoids
over a scheme satisfies the Rim-Schlessinger condition when
all three categories satisfy it. -/
instance instHasRimSchlessinger_twoFibreProduct
    (p : X ⟶ Y) (q : Z ⟶ Y)
    [HasRimSchlessinger X] [HasRimSchlessinger Y] [HasRimSchlessinger Z] :
    HasRimSchlessinger (TwoFibreProduct.apex.{u + 1, u, u + 1, u} p q) := sorry

end AlgebraicGeometry.GroupoidsOver
