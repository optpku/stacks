/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap103.Lemma_103_17_9_Coherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver
open AlgebraicGeometry.AlgebraicStack

universe u

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsLocallyNoetherian X]
variable {F : fppfModules X} {G : QCoh X}
variable [AlgebraicStack.IsCoherent F] [AlgebraicStack.IsCoherent G.obj]

/- Lemma 103.17.9: Let `X` be a locally Noetherian algebraic stack. Let `F` and `G`
be coherent `𝒪_X`-modules. Then the internal hom `hom(F, G)` constructed in
Lemma 103.10.8 is a coherent `𝒪_X`-module. -/
@[stacks 0GRD]
#check (isCoherent_internalHomFP :
  AlgebraicStack.IsCoherent (QCoh.internalHomFP F G).obj)
