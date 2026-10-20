module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable

/-!
# Second diagonal representable by algebraic spaces

For a category fibred in groupoids over `(Sch/S)_fppf`, representability of the
second diagonal by algebraic spaces is equivalent to representability of the
diagonal of every 2-fibre product of that first diagonal along a scheme-slice
test of `X × X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory CategoryTheory.TwoFibreProduct

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The second diagonal of a category fibred in groupoids is representable by
algebraic spaces if and only if every scheme-slice base change of its first
diagonal has diagonal representable by algebraic spaces. -/
@[stacks 07WG]
theorem relativelyRepresentableByAlgebraicSpaces.secondDiagonal_iff
    {S : Scheme.{u}} (X : GroupoidsOver S) :
    relativelyRepresentableByAlgebraicSpaces
        (Hom.diagonal.{u + 1, u, u + 1}
          (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X)) ↔
      ∀ {V : Over S}
        (φ : GroupoidsOver.slice V ⟶
          TwoFibreProduct.apex.{u + 1, u, u + 1, u}
            X.baseProjection X.baseProjection),
        relativelyRepresentableByAlgebraicSpaces
          (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1}
            (TwoFibreProduct.apex.{u + 1, u, u + 1, u}
              (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) φ)) :=
  sorry

/-- If the second diagonal of `X` is representable by algebraic spaces, then the
diagonal of every scheme-slice 2-fibre product along `diagonal X` is
representable by algebraic spaces. -/
theorem relativelyRepresentableByAlgebraicSpaces.pullbackDiagonals_of_secondDiagonal
    {S : Scheme.{u}} (X : GroupoidsOver S)
    (h : relativelyRepresentableByAlgebraicSpaces
      (Hom.diagonal.{u + 1, u, u + 1}
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X)))
    {V : Over S}
    (φ : GroupoidsOver.slice V ⟶
      TwoFibreProduct.apex.{u + 1, u, u + 1, u}
        X.baseProjection X.baseProjection) :
    relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1}
        (TwoFibreProduct.apex.{u + 1, u, u + 1, u}
          (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) φ)) :=
  (relativelyRepresentableByAlgebraicSpaces.secondDiagonal_iff X).mp h φ

/-- If every scheme-slice 2-fibre product along `diagonal X` has diagonal
representable by algebraic spaces, then the second diagonal of `X` is
representable by algebraic spaces. -/
theorem relativelyRepresentableByAlgebraicSpaces.secondDiagonal_of_pullbackDiagonals
    {S : Scheme.{u}} (X : GroupoidsOver S)
    (h : ∀ {V : Over S}
        (φ : GroupoidsOver.slice V ⟶
          TwoFibreProduct.apex.{u + 1, u, u + 1, u}
            X.baseProjection X.baseProjection),
      relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1}
          (TwoFibreProduct.apex.{u + 1, u, u + 1, u}
            (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) φ))) :
    relativelyRepresentableByAlgebraicSpaces
      (Hom.diagonal.{u + 1, u, u + 1}
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X)) :=
  (relativelyRepresentableByAlgebraicSpaces.secondDiagonal_iff X).mpr h

end AlgebraicGeometry
