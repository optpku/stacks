/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.DeligneMumford
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Prestable.Genus

/-!
# Smoothness of the moduli of prestable curves

The prestable locus and each fixed-genus prestable locus are fibred in
groupoids over `Over S`, and their canonical structure morphisms are smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack.Hom renaming Smooth → GroupoidSmooth
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The full subcategory of `𝒞urves` cut out by `prestable` is fibred in
groupoids over `Over S`. -/
instance instIsFiberedInGroupoids_prestable (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids ((prestable S).ι ⋙ p S) :=
  sorry

/-- The full subcategory of `𝒞urves` cut out by `prestableOfGenus g` is
fibred in groupoids over `Over S`. -/
instance instIsFiberedInGroupoids_prestableOfGenus (g : ℕ) (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids ((prestableOfGenus g S).ι ⋙ p S) :=
  sorry

/-- The canonical structure morphism of the prestable moduli stack over `S`
is smooth. -/
@[stacks 0E6W]
instance instSmooth_prestable (S : Scheme.{u}) :
    GroupoidSmooth
      (inclusionOf (prestable S) ≫ CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

/-- The canonical structure morphism of the genus-`g` prestable moduli stack
over `S` is smooth. -/
@[stacks 0E6W]
instance instSmooth_prestableOfGenus (g : ℕ) (S : Scheme.{u}) :
    GroupoidSmooth
      (inclusionOf (prestableOfGenus g S) ≫
        CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
