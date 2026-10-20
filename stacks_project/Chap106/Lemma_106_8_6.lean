/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth.AffineLift
import StacksCheckRecall

/-!
# Lifting along a smooth structure morphism

A morphism from an affine scheme into a smooth algebraic stack over an affine
first-order thickening lifts along that thickening.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Smooth

/- Lemma 106.8.6. If `i : T ⟶ T'` is a first-order thickening of affine
schemes and `X'` is an algebraic stack over `T'` whose structure morphism
`f : X' ⟶ GroupoidsOver.slice T'` is smooth, then any morphism `x` from `T`
to `X'` over `T'` lifts along `i` to a dotted arrow `x' : T' ⟶ X'` over `T'`
with `x'|_T = x`. -/
@[stacks 0DNZ] #check (AlgebraicGeometry.AlgebraicStack.Smooth.exists_lift :
    ∀ {S : Scheme.{u}} {X' : GroupoidsOver S} [AlgebraicStack X']
    {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (i : T ⟶ T')
    [IsFirstOrderThickening i.left] (f : X' ⟶ GroupoidsOver.slice T') [Smooth f]
    (x : GroupoidsOver.slice T ⟶ X')
    (γ : overMap i ≫ 𝟙 (GroupoidsOver.slice T') ≅ x ≫ f),
    Nonempty (DottedArrow (⟨GroupoidsOver.slice T, overMap i, x, γ⟩ :
      Bicategory.PseudoPullbackCone (𝟙 (GroupoidsOver.slice T')) f)))

/- The lift has restriction and structure-map comparisons compatible with γ. -/
#check (AlgebraicGeometry.AlgebraicStack.Smooth.exists_hom :
    ∀ {S : Scheme.{u}} {X' : GroupoidsOver S} [AlgebraicStack X']
    {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (i : T ⟶ T')
    [IsFirstOrderThickening i.left] (f : X' ⟶ GroupoidsOver.slice T') [Smooth f]
    (x : GroupoidsOver.slice T ⟶ X')
    (γ : overMap i ≫ 𝟙 (GroupoidsOver.slice T') ≅ x ≫ f),
    ∃ (x' : GroupoidsOver.slice T' ⟶ X') (α : slice.pullback i x' ≅ x)
      (β : 𝟙 (GroupoidsOver.slice T') ≅ x' ≫ f),
      whiskerLeftIso (overMap i) β ≪≫ (α_ (overMap i) x' f).symm ≪≫
        whiskerRightIso α f = γ)

end AlgebraicGeometry.AlgebraicStack.Smooth
