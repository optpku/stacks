/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Semistable.Genus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.DeligneMumford
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Smooth

/-!
# Smoothness of the moduli stacks of semistable curves

The structure morphisms of semistable curves and of their fixed-genus loci
are smooth over any base scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The full subcategory of `𝒞urves` cut out by `semistable` is fibred in
groupoids over `Over S`. -/
instance instIsFiberedInGroupoids_semistable (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids ((semistable S).ι ⋙ p S) :=
  sorry

/-- The full subcategory of `𝒞urves` cut out by `semistableOfGenus g` is
fibred in groupoids over `Over S`. -/
instance instIsFiberedInGroupoids_semistableOfGenus (g : ℕ) (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids ((semistableOfGenus g S).ι ⋙ p S) :=
  sorry

/-- The canonical structure morphism of the moduli stack of semistable curves
over any base scheme is smooth. -/
@[stacks 0E72]
theorem instSmooth_semistable (S : Scheme.{u}) :
    CohStack.Hom.Smooth
      (inclusionOf (semistable S) ≫ CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

/-- The canonical structure morphism of the moduli stack of semistable curves
of genus `g` over any base scheme is smooth. -/
@[stacks 0E72]
theorem instSmooth_semistableOfGenus (g : ℕ) (S : Scheme.{u}) :
    CohStack.Hom.Smooth
      (inclusionOf (semistableOfGenus g S) ≫
        CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
