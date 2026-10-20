/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.Splitting
import StacksCheckRecall

/-!
@stack 017S
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial

universe u

noncomputable section

namespace SSet

variable {U V : SSet.{u}} (f : U ⟶ V)
variable (hPreserves : SSet.preservesNondegenerate f)

/- Lemma 14.18.3 (1): injectivity on nondegenerate simplices implies degreewise injectivity. -/
@[stacks 017S "injective case"]
#check ((SSet.nonDegenerate.map.injective_iff f hPreserves).mp :
  (∀ n : ℕ, Function.Injective (SSet.nonDegenerate.map f hPreserves n)) →
    ∀ n : ℕ, Function.Injective (f.app (op ⦋n⦌)))

/- Lemma 14.18.3 (2): surjectivity on nondegenerate simplices implies degreewise
surjectivity. -/
@[stacks 017S "surjective case"]
#check ((SSet.nonDegenerate.map.surjective_iff f hPreserves).mp :
  (∀ n : ℕ, Function.Surjective (SSet.nonDegenerate.map f hPreserves n)) →
    ∀ n : ℕ, Function.Surjective (f.app (op ⦋n⦌)))

/- Lemma 14.18.3 (3): bijectivity on nondegenerate simplices implies degreewise bijectivity. -/
@[stacks 017S "bijective case"]
#check ((SSet.nonDegenerate.map.bijective_iff f hPreserves).mp :
  (∀ n : ℕ, Function.Bijective (SSet.nonDegenerate.map f hPreserves n)) →
    ∀ n : ℕ, Function.Bijective (f.app (op ⦋n⦌)))

end SSet
