/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.FormalObjectSystem
public import ReasLib.AlgebraicGeometry.FormalObjectSystem.LimitComparison
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreserving
public import ReasLib.AlgebraicGeometry.GroupoidsOver.OpennessOfVersality
public import ReasLib.AlgebraicGeometry.GroupoidsOver.StrongRimSchlessinger

/-!
# Strong formal effectiveness and openness of versality

Effectiveness of formal object systems with pairwise square-zero transition
kernels implies openness of versality under representability of the diagonal,
the strong Rim-Schlessinger condition, and limit preservation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- A category fibred in groupoids over a locally Noetherian scheme satisfies
openness of versality if its diagonal is representable by algebraic spaces, it
satisfies the strong Rim-Schlessinger condition and is limit preserving, and
every formal object system with pairwise square-zero transition kernels is
effective. -/
theorem OpennessOfVersality.of_squareZeroKernelEffectiveness
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X] [Groupoids.LimitPreserving X]
    (h_diag : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    (h_eff : ∀ ξ : FormalObjectSystem X.p, ξ.KernelSquareZero → ξ.IsEffective) :
    OpennessOfVersality X :=
  sorry

end AlgebraicGeometry.GroupoidsOver

namespace AlgebraicGeometry.Groupoids.Hom

open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids

/-- Over a locally Noetherian scheme, a limit-preserving category fibred in
groupoids satisfying the strong Rim-Schlessinger condition has openness of
versality of its diagonal if its double diagonal is representable by algebraic
spaces and the limit-fibre comparison is fully faithful for every formal object
system with pairwise square-zero transition kernels. -/
theorem OpennessOfVersality.diagonal_of_squareZeroKernelFullyFaithful
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X] [Groupoids.LimitPreserving X]
    (h_ddiag :
      relativelyRepresentableByAlgebraicSpaces
        (Hom.diagonal.{u + 1, u, u + 1}
          (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X)))
    (h_ff :
      ∀ ξ : FormalObjectSystem X.p,
        ξ.KernelSquareZero → ξ.IsLimitComparisonFullyFaithful) :
    OpennessOfVersality
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
