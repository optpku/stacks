/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Group.Action.Weight
import StacksCheckRecall

@[expose] public section

universe u v w

/- 46.3.6.1: for maps modeling `F(p), F(a) : F(B) → F(B[t, t⁻¹])`, the
weight-`k` part of `F(B)` is the set of `ξ` such that
`t ^ k • F(p)(ξ) = F(a)(ξ)`. -/
@[stacks 06UY] #check
  (MulAction.weightPiece :
    {G : Type u} → {M : Type v} → {N : Type w} → [Group G] → [MulAction G N] →
      G → ℤ → (M → N) → (M → N) → Set M)

#check
  (MulAction.mem_weightPiece :
    {G : Type u} → {M : Type v} → {N : Type w} → [Group G] → [MulAction G N] →
      (t : G) → (k : ℤ) → (mapP mapA : M → N) → (ξ : M) →
        (ξ ∈ MulAction.weightPiece t k mapP mapA ↔ t ^ k • mapP ξ = mapA ξ))
