/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PolarizedCurves.Family
public import ReasLib.AlgebraicGeometry.Polarized.Groupoids
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell

/-!
# Groupoid fibrations of polarized curves

Polarized curve families form a category fibred in groupoids over schemes over
`Spec ℤ`, with a canonical inclusion into polarized proper scheme families.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.PolarizedCurves

/-- The base-scheme functor of polarized curves, viewed over `Spec ℤ`, is
fibred in groupoids. -/
instance instIsFiberedInGroupoids_toOverSpecZ :
    Functor.IsFibered.InGroupoids (p ⋙ Polarized.schemeToOverSpecZ) :=
  sorry

/-- Polarized curves, bundled as a category fibred in groupoids over schemes
over `Spec ℤ`. -/
def toGroupoidsOverSpecZ : GroupoidsOver Polarized.specZ :=
  Groupoids.ofFunctor.{u + 1, u, u + 1, u} (p ⋙ Polarized.schemeToOverSpecZ)

/-- The projection of the bundled category of polarized curves over `Spec ℤ`
is its base-scheme functor followed by the canonical functor to the slice. -/
theorem toGroupoidsOverSpecZ_p :
    toGroupoidsOverSpecZ.p = p ⋙ Polarized.schemeToOverSpecZ :=
  rfl

/-- The full-subcategory inclusion of polarized curves into polarized proper
scheme families, as a morphism of groupoid fibrations over `Spec ℤ`. -/
def inclusionHom : toGroupoidsOverSpecZ ⟶ Polarized.toGroupoidsOverSpecZ :=
  Groupoids.ofBasedFunctor
    { toFunctor := inclusion
      w := rfl }

/-- The underlying functor of the inclusion of groupoid fibrations is the
full-subcategory inclusion of polarized curves. -/
theorem inclusionHom_toFunctor :
    Groupoids.toFunctor inclusionHom = inclusion :=
  rfl

/-- The inclusion of polarized curves strictly commutes with the projections
to schemes over `Spec ℤ`. -/
theorem inclusionHom_comm :
    Groupoids.toFunctor inclusionHom ⋙ Polarized.toGroupoidsOverSpecZ.p =
      toGroupoidsOverSpecZ.p :=
  Groupoids.comm inclusionHom

end AlgebraicGeometry.PolarizedCurves
