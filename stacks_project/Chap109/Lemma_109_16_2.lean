/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap108.Lemma_108_8_5_Smooth
public import stacks_project.Chap109.Lemma_109_7_3_Substack
public import stacks_project.Chap109.Lemma_109_16_1_Substack

/-!
# Smooth curves as a stack

The open substack `𝒞urves^{smooth} ⊂ 𝒞urves` has smooth structure morphism to
`Spec(Z)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The full subcategory of `𝒞urves` cut out by `smooth` is fibred in
groupoids over `Over S`. -/
instance instIsFiberedInGroupoids_smooth (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids ((smooth S).ι ⋙ p S) :=
  sorry

/-- Lemma 109.16.2: the morphism `𝒞urves^{smooth} ⟶ Spec(Z)`, namely
`inclusionOf (smooth S) ≫ CohStack.toIdentitySlice (toGroupoids S)`, is
smooth. -/
@[stacks 0E1N]
instance instSmooth_smooth (S : Scheme.{u}) :
    CohStack.Hom.Smooth
      (inclusionOf (smooth S) ≫ CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
