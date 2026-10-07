module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.Degree

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AbelianVariety

universe u

/- Lemma 39.9.8: multiplication by a nonzero natural number `d` on an abelian variety `A` is
finite locally free of degree `d ^ (2 * AbelianVariety.dimension A)`. -/
@[stacks 0BFG] #check
  (AlgebraicGeometry.AbelianVariety.instIsFiniteLocallyFreeOfRankMulBy :
    ∀ {k : Type u} [Field k] (A : SchemeOverField k) [GrpObj A] [AbelianVariety A]
      (d : ℕ) [NeZero d],
      IsFiniteLocallyFreeOfRank ([d]ₐ A) (d ^ (2 * AbelianVariety.dimension A)))
