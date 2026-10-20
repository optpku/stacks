/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalDeformation.Products
public import ReasLib.AlgebraicGeometry.GroupoidsOver.ObstructionTheory.Products
public import ReasLib.AlgebraicGeometry.GroupoidsOver.OpennessOfVersality
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreserving
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Let `S` be a locally Noetherian scheme. Let `X` be a
category fibred in groupoids over `(Sch/S)_fppf`. Assume the diagonal
`Δ : X ⟶ X × X` is representable by algebraic spaces, `X` has (RS*), `X` is
limit preserving, there is an obstruction theory `𝒪`, and for an object `x`
of `X` over `Spec(A)` and `A`-modules `M n` the comparison
`T_x(∏ᶜ M) ⟶ ∏ᶜ T_x(M n)` is an isomorphism and
`O_x(∏ᶜ M) ⟶ ∏ᶜ O_x(M n)` is injective. Then `X` satisfies openness of
versality. -/
theorem OpennessOfVersality.ofObstructionTheory
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X] [Groupoids.LimitPreserving X]
    (h_diag : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    (𝒪 : ObstructionTheory X) (hT : tangentFunctor.preservesNatPi X)
    (hO : 𝒪.natPiComparison_injective) :
    OpennessOfVersality X :=
  sorry
end AlgebraicGeometry.GroupoidsOver
