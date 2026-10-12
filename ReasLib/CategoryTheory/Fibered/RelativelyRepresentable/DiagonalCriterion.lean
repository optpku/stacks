/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

-- `HasPullback` is public because the exported criterion assumes `Limits.HasPullbacks C`.
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.BaseChange
public import ReasLib.CategoryTheory.Fibered.RelativelyRepresentable.DiagonalBaseChange.Comparison.OverBase

/-!
# Relative representability and diagonal morphisms

For a category fibred in groupoids, relative representability of the canonical diagonal is
equivalent to relative representability of every morphism from a slice fibration. The two
directions are exposed separately for downstream use.
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids.relativelyRepresentable

/-- If the diagonal of `X` is relatively representable, then every morphism
`G : C/U ⟶ X` from a slice fibration is relatively representable. -/
theorem slices_of_diagonal
    [Limits.HasBinaryProducts C] {X : FiberedCategoryOver.Groupoids C}
    (h_diagonal : relativelyRepresentable (diagonal X)) :
    ∀ {U : C} (G : slice U ⟶ X), relativelyRepresentable G := sorry
/- Proof strategy: use `iff_forall_twoFibreProduct` on both the diagonal and each `G`. For a test
`G' : C/V ⟶ X`, choose the terminal comparison maps from `ProductSlice.sourceSquare G G'`
and `PseudoPullbackCone.diagonal X` to the canonical two-fibre-product cone. The diagonal
hypothesis supplies representability after the second comparison; transport it to
`TwoFibreProduct.apex G' G` with `ProductSlice.DiagonalBaseChange.representable.source`. -/

/-- If every morphism `G : C/U ⟶ X` from a slice fibration is relatively representable, then
the canonical diagonal of `X` is relatively representable. -/
theorem diagonal_of_slices
    [Limits.HasBinaryProducts C] [Limits.HasPullbacks C]
    {X : FiberedCategoryOver.Groupoids C} (h_all :
      ∀ {U : C} (G : slice U ⟶ X), relativelyRepresentable G) :
    relativelyRepresentable (diagonal X) := sorry
/- Proof strategy:
1. Use `iff_forall_twoFibreProduct` to fix a slice test `H : C/W ⟶ X ×_C X`.
2. Compose `H` with both projections and apply `h_all` to obtain representability of their
   absolute two-fibre product.
3. Compare the product-slice source square with the canonical diagonal base change using
   `ProductSlice.DiagonalBaseChange.representable.ofProduct`.
4. Transport along `PseudoPullbackComparison.iso`, the canonical diagonal comparison, and
   `BasedCategory.PseudoPullback.Comparison.equivalence`. -/

/-- Relative representability of the canonical diagonal of `X` is equivalent to relative
representability of every morphism from a slice fibration. -/
@[stacks 02YA]
theorem diagonal_iff
    [Limits.HasBinaryProducts C] [Limits.HasPullbacks C] (X : FiberedCategoryOver.Groupoids C) :
    relativelyRepresentable (diagonal X) ↔
      ∀ {U : C} (G : slice U ⟶ X), relativelyRepresentable G := sorry
/- Proof strategy: combine `slices_of_diagonal` and `diagonal_of_slices`. -/

end FiberedCategoryOver.Groupoids.relativelyRepresentable

end CategoryTheory
