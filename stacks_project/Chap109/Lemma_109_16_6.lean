/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Smooth
public import stacks_project.Chap109.Lemma_109_7_3_Substack
public import stacks_project.Chap109.Lemma_109_16_5_Substack

/-!
# Smoothness of the moduli stacks of smooth proper curves

The structure morphisms `ℳ ⟶ Spec(Z)` and `ℳ_g ⟶ Spec(Z)` are smooth,
where `ℳ` is the moduli stack of smooth proper curves and `ℳ_g` is the
open-and-closed genus-`g` piece.
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

/-- Lemma 109.16.6 (1): the structure morphism `ℳ ⟶ Spec(Z)` is
smooth. -/
@[stacks 0E84]
instance instSmooth_smoothH0 (S : Scheme.{u}) :
    CohStack.Hom.Smooth
      (inclusionOf (smoothH0 S) ≫ CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

/-- Lemma 109.16.6 (2): the structure morphism `ℳ_g ⟶ Spec(Z)` is
smooth. -/
@[stacks 0E84]
instance instSmooth_smoothH0OfGenus (g : ℕ) (S : Scheme.{u}) :
    CohStack.Hom.Smooth
      (inclusionOf (smoothH0OfGenus g S) ≫
        CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
