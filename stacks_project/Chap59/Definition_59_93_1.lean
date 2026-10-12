/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Definition_59_93_1_LocalAcyclicity
import StacksCheckRecall

/- Definition 59.93.1 (1): a morphism `f : X ⟶ S` is locally acyclic at a geometric point
`xbar` of `X` relative to an object `K` of `D(X_etale)` if for every geometric point
`tbar` of `Spec(O^sh_{S, f(xbar)})` the comparison map `etaleCohomologyAlpha` is an
isomorphism. The comparison is expressed using derived sections on the strict
henselization, the canonical presentation of the geometric stalk. -/
@[stacks 0GJP] #check AlgebraicGeometry.Scheme.LocallyAcyclicAt

/- Definition 59.93.1 (2): `f` is locally acyclic relative to `K` if it is locally acyclic
at every geometric point of `X` relative to `K`. -/
@[stacks 0GJP] #check AlgebraicGeometry.Scheme.LocallyAcyclicRelative

/- Definition 59.93.1 (3): `f` is universally locally acyclic relative to `K` if every
base change `f' : X' ⟶ S'` is locally acyclic relative to the inverse image of `K`. -/
@[stacks 0GJP] #check AlgebraicGeometry.Scheme.UniversallyLocallyAcyclicRelative

/- Definition 59.93.1 (4): `f` is locally acyclic if for every geometric point `xbar` of `X`
and every integer `n` prime to the characteristic of `κ(xbar)`, `f` is locally acyclic at
`xbar` relative to the constant sheaf with value `ℤ/nℤ`. -/
@[stacks 0GJP] #check AlgebraicGeometry.Scheme.LocallyAcyclic

/- Definition 59.93.1 (5): `f` is universally locally acyclic if every base change
`f' : X' ⟶ S'` is locally acyclic. -/
@[stacks 0GJP] #check AlgebraicGeometry.Scheme.UniversallyLocallyAcyclic
