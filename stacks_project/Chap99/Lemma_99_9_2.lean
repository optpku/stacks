/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap99.Lemma_99_9_2_Comparison

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

/- Lemma 99.9.2: in Situation 99.9.1, the Hilbert functor Hilb_{X/B} equals the
Quot functor Quot_{𝒪_X/X/B} as functors (Sch/B)ᵒᵖ ⥤ Sets. The identification
sends a closed subspace Z ⊂ X_T with Z ⟶ T of finite presentation, flat, and
proper to the quotient 𝒪_{X_T} ⟶ ι_* 𝒪_Z, and conversely cuts out Z from
I = Ker(𝒪_{X_T} ⟶ Q). -/
@[stacks 0D00] #check AlgebraicGeometry.AlgebraicSpace.Hilbert.quotIso
