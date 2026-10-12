/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Smooth
public import stacks_project.Chap109.Lemma_109_7_3_Substack
public import stacks_project.Chap109.Lemma_109_18_1_Substack

/-!
# Smoothness of the structure morphism of nodal curves

The open substack `𝒞urves^{nodal} ⊂ 𝒞urves` has smooth structure morphism to
`Spec(Z)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.ObjectProperty
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The full subcategory of `𝒞urves` cut out by `nodal` is fibred in
groupoids over `Over S`. -/
instance instIsFiberedInGroupoids_nodal (S : Scheme.{u}) :
    Functor.IsFibered.InGroupoids ((nodal S).ι ⋙ p S) :=
  sorry

/-- Lemma 109.18.2: the structure morphism `𝒞urves^{nodal} ⟶ Spec(Z)` is
smooth. -/
@[stacks 0E00]
instance instSmooth_nodal (S : Scheme.{u}) :
    CohStack.Hom.Smooth
      (inclusionOf (nodal S) ≫ CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
