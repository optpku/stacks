/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap93.Lemma_93_8_8_Henselization
import StacksCheckRecall

/-!
# Henselization of ring deformations
-/

@[expose] public section

open CategoryTheory FlatAlgebraCat

/- Lemma 93.8.8: in Example 93.8.1, if `P` is a `k`-algebra and `J ⊂ P` is an
ideal, with `(P^h, J^h)` the henselization of the pair `(P, J)` given by
`henselizationRing (pairOfIdeal J)` and `henselizationIdeal (pairOfIdeal J)`,
there is a natural functor `Def_P ⟶ Def_{P^h}` of deformation categories,
sending a deformation `(A, Q) ⟶ (k, P)` to `(A, Q^h) ⟶ (k, P^h)`. -/
@[stacks 0DYT]
#check @FlatAlgebraCat.henselizationFunctor

end
