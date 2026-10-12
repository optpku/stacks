/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Lemma_92_3_4_DirectLimit
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u

open CategoryTheory

namespace Algebra.CotangentComplex.DirectLimit

/-- Lemma 92.3.4: Let `A_i → B_i` be a system of ring maps over a directed index set `I`.
Then `colim L_{B_i/A_i} = L_{colim B_i / colim A_i}`. -/
@[stacks 08S9, instance]
theorem comparison_isIso
    {I : Type u} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    {R S : I → Type u}
    [∀ i, CommRing (R i)] [∀ i, CommRing (S i)] [∀ i, Algebra (R i) (S i)]
    (ρ : ∀ i j, i ≤ j → R i →+* R j)
    (σ : ∀ i j, i ≤ j → S i →+* S j)
    [DirectedSystem R (fun i j h ↦ ρ i j h)]
    [DirectedSystem S (fun i j h ↦ σ i j h)]
    (hcomm :
      ∀ ⦃i j : I⦄ (h : i ≤ j),
        (algebraMap (R j) (S j)).comp (ρ i j h) =
          (σ i j h).comp (algebraMap (R i) (S i))) :
    IsIso (comparison ρ σ hcomm) :=
  sorry

end Algebra.CotangentComplex.DirectLimit
