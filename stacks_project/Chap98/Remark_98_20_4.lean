/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.OpennessOfVersality.StrongEffectiveness
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.Groupoids.Hom

universe u

/- Remark 98.20.4: let `S` be a locally Noetherian scheme and let `X` be a
category fibred in groupoids over `(Sch/S)_fppf`. Assume the double diagonal
`Hom.diagonal (diagonal X) : X ⟶ X ×_{X × X} X` is representable by algebraic
spaces, `X` has (RS*), `X` is limit preserving, and for inverse systems of
`S`-algebras as in Remark 98.20.2 with `Ker(R_m ⟶ R_n)` square zero for all
`m ≥ n` the functor `X_{Spec(lim R_n)} ⟶ lim_n X_{Spec(R_n)}` is fully
faithful. Then the diagonal `Δ : X ⟶ X × X` satisfies openness of versality.
This follows by applying Lemma 98.20.3 to the slices
`fiberProductSlice (diagonal X) hV y hy` for affine `V` locally of finite
presentation over `S` and objects `y` of `X × X` over `V`. The source leaves
a detailed proof to a future conversion of this remark into a lemma. -/
@[stacks 0CXV] #check
  (AlgebraicGeometry.Groupoids.Hom.OpennessOfVersality.diagonal_of_squareZeroKernelFullyFaithful :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X] [Groupoids.LimitPreserving X]
    (h_ddiag :
      relativelyRepresentableByAlgebraicSpaces
        (Hom.diagonal.{u + 1, u, u + 1}
          (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X)))
    (h_ff :
      ∀ ξ : FormalObjectSystem X.p,
        ξ.KernelSquareZero → ξ.IsLimitComparisonFullyFaithful),
    OpennessOfVersality
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
