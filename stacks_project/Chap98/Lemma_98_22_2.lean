/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.ObstructionTheory.OpennessOfVersality
import StacksCheckRecall

/-!
# Obstruction theories imply openness of versality

On a locally Noetherian base, a category fibred in groupoids over `(Sch/S)_fppf`
with diagonal representable by algebraic spaces, (RS*), limit preservation, an
obstruction theory, countable-product preservation of `T_x`, and injective
countable-product comparison of `O_x`, satisfies openness of versality.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver

universe u

/- Lemma 98.22.2: a category fibred in groupoids over a locally Noetherian
scheme satisfies openness of versality if its diagonal is representable by
algebraic spaces, it satisfies (RS*) and limit preservation, and an obstruction
theory has invertible tangent and injective obstruction countable-product
comparisons. -/
@[stacks 0CYF] #check (AlgebraicGeometry.GroupoidsOver.OpennessOfVersality.ofObstructionTheory :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    [HasStrongRimSchlessinger X] [Groupoids.LimitPreserving X]
    (h_diag : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))
    (𝒪 : ObstructionTheory X) (hT : tangentFunctor.preservesNatPi X)
    (hO : 𝒪.natPiComparison_injective),
    OpennessOfVersality X)
