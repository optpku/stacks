/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Lemma_87_20_10_Types
import StacksCheckRecall

@[expose] public section

/- Definition 87.20.7 (1): for a scheme `S` and a formal algebraic space `X`
over `S`, we say `X` is locally countably indexed if the equivalent
conditions of Lemma 87.20.6 hold for the countably indexed affine type. -/
@[stacks 0AKY] #check AlgebraicGeometry.IsLocallyCountablyIndexed

/- Definition 87.20.7 (2): for a scheme `S` and a formal algebraic space `X`
over `S`, we say `X` is locally countably indexed and classical if the
equivalent conditions of Lemma 87.20.6 hold for the corresponding affine
type. -/
@[stacks 0AKY] #check AlgebraicGeometry.IsLocallyClassical

/- Definition 87.20.7 (3): for a scheme `S` and a formal algebraic space `X`
over `S`, we say `X` is locally weakly adic if the equivalent conditions of
Lemma 87.20.6 hold for the weakly adic affine type. -/
@[stacks 0AKY] #check AlgebraicGeometry.IsLocallyWeaklyAdic

/- Definition 87.20.7 (4): for a scheme `S` and a formal algebraic space `X`
over `S`, we say `X` is locally adic* if the equivalent conditions of
Lemma 87.20.6 hold for the adic* affine type. -/
@[stacks 0AKY] #check AlgebraicGeometry.IsLocallyAdicStar

/- Definition 87.20.7 (5): for a scheme `S` and a formal algebraic space `X`
over `S`, we say `X` is locally Noetherian if the equivalent conditions of
Lemma 87.20.6 hold for the Noetherian affine type. -/
@[stacks 0AKY] #check AlgebraicGeometry.IsFormalAlgebraicSpace.IsLocallyNoetherian
