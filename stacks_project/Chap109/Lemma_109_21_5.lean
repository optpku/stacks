/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Smooth
public import stacks_project.Chap109.Lemma_109_7_3_Substack
public import stacks_project.Chap109.Lemma_109_21_4_Substack

/-!
# Smoothness of the moduli stacks of semistable curves

The structure morphisms `𝒞urves^{semistable} ⟶ Spec(Z)` and
`𝒞urves^{semistable}_g ⟶ Spec(Z)` are smooth.
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

/-- Lemma 109.21.5 (1): the structure morphism `𝒞urves^{semistable} ⟶ Spec(Z)`
is smooth. -/
@[stacks 0E72]
instance instSmooth_semistable (S : Scheme.{u}) :
    CohStack.Hom.Smooth
      (inclusionOf (semistable S) ≫ CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

/-- Lemma 109.21.5 (2): the structure morphism
`𝒞urves^{semistable}_g ⟶ Spec(Z)` is smooth. -/
@[stacks 0E72]
instance instSmooth_semistableOfGenus (g : ℕ) (S : Scheme.{u}) :
    CohStack.Hom.Smooth
      (inclusionOf (semistableOfGenus g S) ≫
        CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
