/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap103.Definition_103_17_2_Coh
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver

universe u

/- Definition 103.17.2 (1): let `X` be a locally Noetherian algebraic stack. An
`𝒪_X`-module `F` is called coherent if `F` satisfies one (and hence all) of the
equivalent conditions of Lemma 103.17.1. -/
@[stacks 0GR6] #check AlgebraicStack.IsCoherent

/- Definition 103.17.2 (2): the category of coherent `𝒪_X`-modules is denoted
`Coh(𝒪_X)`. -/
@[stacks 0GR6] #check AlgebraicStack.Coh

/- Coherence of an `𝒪_X`-module on a locally Noetherian algebraic stack is
equivalent to finite presentation. -/
#check AlgebraicStack.isCoherent_iff

/- The forgetful inclusion `Coh(𝒪_X) ⥤ Mod(𝒪_X)`. -/
#check AlgebraicStack.Coh.inclusion
