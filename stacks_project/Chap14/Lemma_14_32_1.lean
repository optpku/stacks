/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.TrivialKanFibration.Coskeletal
import StacksCheckRecall

/-!
@stack 01A6

# Lemma 14.32.1 compatibility facade

ReasLib exposes both the concrete simplicial-set criterion and its categorical `IsIso`/`Epi`
variant; both conclude with the canonical owner predicate `I.rlp`.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial
open SSet.modelCategoryQuillen

universe u

variable {V U : SSet.{u}} (f : V ⟶ U) (n : ℕ)

/- Lemma 14.32.1: degreewise bijectivity below `n`, surjectivity in degree `n`, and
`n`-coskeletality of source and target imply that `f` is a trivial Kan fibration. -/
@[stacks 01A6]
#check (I.rlp.coskeletal.ofBijective.explicit f n :
  (∀ i < n, Function.Bijective (f.app (op ⦋i⦌))) →
    Function.Surjective (f.app (op ⦋n⦌)) →
      V.IsCoskeletal n → U.IsCoskeletal n → I.rlp f)

#check I.rlp.coskeletal.ofIsIso.explicit f n
