/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap77.Lemma_77_12_7_ProperSupport
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace.Modules

/- Lemma 77.12.7: in Situation 77.12.1, with `K` as in Lemma 77.12.2 and
`W ⊂ X` as in Lemma 77.12.6, after possibly shrinking the open `W`, the
support of `ℱ = H^0(K)|_W` is proper over `A`. -/
@[stacks 0CXA] #check ProperFlatFormalSystem.existsOpen_coheratorLimit_hasProperSupport
