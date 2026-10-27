/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.SmoothH0.Genus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.DeligneMumford
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Smooth

/-!
# Structure morphisms of smooth curve loci

The loci of smooth proper curves with universally trivial structure-sheaf
pushforward, and of such curves of fixed genus, have smooth structure
morphisms over any base scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The full subcategory of `𝒞urves` cut out by `smoothH0` is fibred in
groupoids over `Over S`. -/
instance instIsFiberedInGroupoids_smoothH0 (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids ((smoothH0 S).ι ⋙ p S) :=
  sorry

/-- The full subcategory of `𝒞urves` cut out by `smoothH0OfGenus g` is
fibred in groupoids over `Over S`. -/
instance instIsFiberedInGroupoids_smoothH0OfGenus (g : ℕ) (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids ((smoothH0OfGenus g S).ι ⋙ p S) :=
  sorry

/-- The moduli stack of smooth proper curves with universally trivial
structure-sheaf pushforward and one-dimensional fibres has smooth structure
morphism over `S`. -/
instance instSmooth_smoothH0 (S : Scheme.{u}) :
    CohStack.Hom.Smooth
      (inclusionOf (smoothH0 S) ≫ CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

/-- The moduli stack of smooth proper curves of genus `g` with universally
trivial structure-sheaf pushforward and one-dimensional fibres has smooth
structure morphism over `S`. -/
instance instSmooth_smoothH0OfGenus (g : ℕ) (S : Scheme.{u}) :
    CohStack.Hom.Smooth
      (inclusionOf (smoothH0OfGenus g S) ≫
        CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
