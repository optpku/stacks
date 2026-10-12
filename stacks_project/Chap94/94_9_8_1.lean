/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.«94_9_8_1_Comparison»
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

/- 94.9.8.1: let `F` and `G` be algebraic spaces over `S` representing the
2-fibre product `TwoFibreProduct.apex g f` and the base `Z`. The 1-morphism
`TwoFibreProduct.fst g f` corresponds to a morphism `f' : F ⟶ G` of algebraic
spaces. The right square is the 2-fibre product, with projections
`TwoFibreProduct.fst`, `TwoFibreProduct.snd` and 2-commutativity
`TwoFibreProduct.comparisonIso`. Squiggly arrows are the associated sheaf of
isomorphism classes of a category fibred in setoids, equivalently a representing
equivalence with `AlgebraicSpace.toGroupoids` (compared after `uliftFunctor`
with `Functor.fiberIsoClassPresheaf`). -/
@[stacks 0403]
#check RepresentsTwoFibreProductOnSpace
