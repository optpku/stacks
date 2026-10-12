/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap88.Lemma_88_6_4_EtaleApprox
import StacksCheckRecall

@[expose] public section

/- Lemma 88.6.4: Let A be a Noetherian G-ring, I an ideal of A, and B, C
finite type A-algebras. For any A-algebra map ψ of I-adic completions
B^∧ ⟶ C^∧ and any N ≥ 1, there exist an étale ring map C ⟶ C' inducing an
isomorphism C ⧸ IC ≃ C' ⧸ IC' and an A-algebra map φ : B ⟶ C' such that φ
and ψ agree modulo I^N into C^∧ = (C')^∧. -/
@[stacks 0AK4]
#check @AdicCompletion.EtaleApprox.exists_of_isGRing
