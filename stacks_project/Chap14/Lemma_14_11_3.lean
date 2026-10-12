/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.StdSimplex
import StacksCheckRecall

/-!
@stack 0177
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe u

variable (U : SSet.{u}) (n : ℕ)

/- Lemma 14.11.3: maps from `Δ[n]` to `U` are canonically identified with the `n`-simplices
of `U`. -/
@[stacks 0177]
#check (SSet.yonedaEquiv : (Δ[n] ⟶ U) ≃ U _⦋n⦌)

/- The forward equivalence evaluates a map at the unique top-dimensional nondegenerate simplex,
represented by the identity of `⦋n⦌`. -/
#check (SSet.yonedaEquiv_apply (U := U) (n := n) :
  ∀ f : Δ[n] ⟶ U,
    SSet.yonedaEquiv f =
      f.app (Opposite.op ⦋n⦌) (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)))
