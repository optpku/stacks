/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreserving
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFiniteType

/-!
# Diagonals of limit-preserving categories fibred in groupoids

The absolute diagonal of a limit-preserving category fibred in groupoids is
locally of finite type whenever it is representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids

/-- The absolute diagonal of a limit-preserving category fibred in groupoids
over `(Sch/S)_fppf` is locally of finite type if it is representable by
algebraic spaces. -/
theorem locallyOfFiniteType_diagonal {S : Scheme.{u}} (X : GroupoidsOver S)
    [LimitPreserving X]
    (h_diag : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X)) :
    Hom.LocallyOfFiniteType
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) :=
  sorry

/-- The absolute diagonal of a limit-preserving category fibred in groupoids
is locally of finite type when its representability by algebraic spaces is
available as a fact. -/
instance instLocallyOfFiniteTypeDiagonal {S : Scheme.{u}} (X : GroupoidsOver S)
    [LimitPreserving X]
    [h_diag : Fact (relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))] :
    Hom.LocallyOfFiniteType
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) :=
  locallyOfFiniteType_diagonal X h_diag.out

end AlgebraicGeometry.Groupoids
