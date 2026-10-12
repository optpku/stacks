/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.RelativeDualizing.CompleteIntersection
import StacksCheckRecall

@[expose] public section

universe u v

open scoped Algebra.DualModule

/- Lemma 49.10.3: if a nonzero `k`-algebra `B` is a zero-dimensional global complete
intersection over the field `k`, then `Algebra.DualModule.of k B`, representing
`Hom_k(B, k)` with its canonical `B`-action, is invertible. -/
@[stacks 0DWL] #check (Algebra.DualModule.instInvertibleOfGlobalCompleteIntersection :
  ∀ (k : Type u) (B : Type v) [Field k] [CommRing B] [Algebra k B] [Nontrivial B]
    [IsGlobalCompleteIntersection k B] [Ring.KrullDimLE 0 B],
    Module.Invertible B (Algebra.DualModule.of k B))
