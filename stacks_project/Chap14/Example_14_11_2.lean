module

public import ReasLib.AlgebraicTopology.SimplicialSet.StdSimplex
import StacksCheckRecall

/-!
@stack 0176
-/

@[expose] public section

open CategoryTheory
open SSet.stdSimplex
open scoped Simplicial

universe u

variable (n m : ℕ) (h : n < m)

/- Example 14.11.2 (1): `Δ[n]` is the simplicial set represented by `⦋n⦌`. -/
@[stacks 0176 "Example 14.11.2 (1)"]
#check (SSet.stdSimplex.objEquiv :
  (Δ[n] : SSet.{u}) _⦋m⦌ ≃ (⦋m⦌ ⟶ ⦋n⦌))

/- Example 14.11.2 (2): every simplex of `Δ[n]` in degree strictly above `n` is degenerate. -/
@[stacks 0176 "Example 14.11.2 (2)"]
#check (Δ[n].degenerate_eq_univ_of_hasDimensionLT (n + 1) m h :
  Δ[n].degenerate m = Set.univ)

/- Example 14.11.2 (3): the identity simplex is the unique top-dimensional nondegenerate
simplex of `Δ[n]`. -/
@[stacks 0176 "Example 14.11.2 (3)"]
#check (nonDegenerate.eq_singleton_identity n :
  (Δ[n] : SSet.{u}).nonDegenerate n =
    {objEquiv.symm (𝟙 ⦋n⦌)})
