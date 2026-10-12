/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap109.Lemma_109_16_5_Substack
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/- Definition 109.16.4 (1): we denote ℳ and name it the moduli stack of
smooth proper curves the algebraic stack 𝒞urves^{smooth, h0} parametrizing
families of curves introduced in Lemma 109.16.3. -/
@[stacks 0E82] #check smoothH0

/- Definition 109.16.4 (2): for g ≥ 0 we denote ℳ_g and name it the moduli
stack of smooth proper curves of genus g the algebraic stack introduced in
Lemma 109.16.5. -/
@[stacks 0E82] #check smoothH0OfGenus
