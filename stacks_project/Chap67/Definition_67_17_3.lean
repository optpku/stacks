/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_17_3_SchemeTheoreticDensity
public import stacks_project.Chap67.Lemma_67_16_6_SchemeTheoreticImage
import StacksCheckRecall

@[expose] public section

/- Definition 67.17.3 (1): the scheme-theoretic closure of an open subspace `U`
of an algebraic space `X` over a scheme `S` is the scheme-theoretic image of the
open immersion `U ⟶ X`. -/
@[stacks 0834] #check AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticImage

/- Definition 67.17.3 (2): an open subspace `U` of an algebraic space `X` over a
scheme `S` is scheme-theoretically dense in `X` if the equivalent conditions of
Lemma 67.17.2 are satisfied. -/
@[stacks 0834] #check AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticallyDense
