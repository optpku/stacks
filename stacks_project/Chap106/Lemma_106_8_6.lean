/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Construction
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap103.«103_15_1_1_Smooth»

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

/-- Lemma 106.8.6. If `i : T ⟶ T'` is a first-order thickening of affine
schemes and `X'` is an algebraic stack over `T'` whose structure morphism
`f : X' ⟶ GroupoidsOver.slice T'` is smooth, then any morphism `x` from `T`
to `X'` over `T'` lifts along `i` to a dotted arrow `x' : T' ⟶ X'` over `T'`
with `x'|_T = x`. -/
@[stacks 0DNZ]
theorem exists_lift {S : Scheme.{u}} {X' : GroupoidsOver S} [AlgebraicStack X']
    {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (i : T ⟶ T')
    [IsFirstOrderThickening i.left] (f : X' ⟶ GroupoidsOver.slice T') [Smooth f]
    (x : GroupoidsOver.slice T ⟶ X')
    (γ : overMap i ≫ 𝟙 (GroupoidsOver.slice T') ≅ x ≫ f) :
    Nonempty
      (DottedArrow
        (⟨GroupoidsOver.slice T, overMap i, x, γ⟩ :
          Bicategory.PseudoPullbackCone (𝟙 (GroupoidsOver.slice T')) f)) :=
  sorry

/-- Unpacking of `exists_lift`: there is a morphism `x' : T' ⟶ X'` over `T'`
whose restriction along `i` is isomorphic to `x`. -/
theorem exists_hom {S : Scheme.{u}} {X' : GroupoidsOver S} [AlgebraicStack X']
    {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (i : T ⟶ T')
    [IsFirstOrderThickening i.left] (f : X' ⟶ GroupoidsOver.slice T') [Smooth f]
    (x : GroupoidsOver.slice T ⟶ X')
    (γ : overMap i ≫ 𝟙 (GroupoidsOver.slice T') ≅ x ≫ f) :
    ∃ x' : GroupoidsOver.slice T' ⟶ X',
      Nonempty (slice.pullback i x' ≅ x) ∧
        Nonempty (x' ≫ f ≅ 𝟙 (GroupoidsOver.slice T')) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Smooth
