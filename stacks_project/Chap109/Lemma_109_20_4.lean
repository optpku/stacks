module

public import stacks_project.Chap108.Lemma_108_8_5_Smooth
public import stacks_project.Chap109.Lemma_109_7_3_Substack
public import stacks_project.Chap109.Lemma_109_20_3_Substack

/-!
# Smoothness of the structure morphisms of prestable curves

The structure morphisms `𝒞urves^{prestable} ⟶ Spec(Z)` and
`𝒞urves^{prestable}_g ⟶ Spec(Z)` are smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
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

/-- Lemma 109.20.4 (1): the structure morphism `𝒞urves^{prestable} ⟶ Spec(Z)` is
smooth. -/
@[stacks 0E6W]
instance instSmooth_prestable (S : Scheme.{u}) :
    CohStack.Hom.Smooth
      (inclusionOf (prestable S) ≫ CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

/-- Lemma 109.20.4 (2): the structure morphism `𝒞urves^{prestable}_g ⟶ Spec(Z)` is
smooth. -/
@[stacks 0E6W]
instance instSmooth_prestableOfGenus (g : ℕ) (S : Scheme.{u}) :
    CohStack.Hom.Smooth
      (inclusionOf (prestableOfGenus g S) ≫
        CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
