/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PolarizedCurves.Groupoids
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion

/-!
# Polarized curves as an open and closed substack

The canonical inclusion of polarized curves into polarized proper scheme
families is both an open and a closed immersion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.PolarizedCurves

/-- The canonical inclusion of polarized curves into polarized proper scheme
families is an open and closed immersion. -/
@[stacks 0DPZ]
theorem inclusionHom_isOpenAndClosedImmersion :
    OpenImmersion inclusionHom.{u} ∧ ClosedImmersion inclusionHom.{u} :=
  sorry

/-- The inclusion of polarized curves is an open immersion of groupoid
fibrations over `Spec ℤ`. -/
instance instOpenImmersion_inclusionHom : OpenImmersion inclusionHom :=
  inclusionHom_isOpenAndClosedImmersion.1

/-- The inclusion of polarized curves is a closed immersion of groupoid
fibrations over `Spec ℤ`. -/
instance instClosedImmersion_inclusionHom : ClosedImmersion inclusionHom :=
  inclusionHom_isOpenAndClosedImmersion.2

end AlgebraicGeometry.PolarizedCurves
