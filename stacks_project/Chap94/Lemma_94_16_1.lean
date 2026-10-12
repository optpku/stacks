/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Lemma_94_16_1_Groupoid
public import stacks_project.Chap94.Lemma_94_16_1_KernelPair
public import stacks_project.Chap94.Lemma_94_16_1_QuotientMap
import StacksCheckRecall

/-!
# Lemma 94.16.1

From a 1-morphism `f : U ⟶ X` out of a space-representable algebraic stack one
obtains the kernel-pair groupoid in algebraic spaces and a fully faithful
1-morphism `[U/R] ⟶ X`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack

/- Lemma 94.16.1 (1): the self 2-fibre product `R = U ×_{f, X, f} U` is representable
by an algebraic space. -/
@[stacks 04T4]
#check kernelPair_isRepresentableByAlgebraicSpace

/- Lemma 94.16.1 (2): there is a canonical equivalence
`U ×_{f, X, f} U ×_{f, X, f} U ≌ R ×_{pr₁, U, pr₀} R`. -/
@[stacks 04T4]
#check tripleEquiv

/- Lemma 94.16.1 (3): the projection `pr₀₂` induces, via the equivalence (2), a
1-morphism `R ×_{pr₁, U, pr₀} R ⟶ R`. -/
@[stacks 04T4]
#check pr02

/- Lemma 94.16.1 (4): if `U, R` are algebraic spaces representing `U, R` and
`t, s : R ⟶ U` and `c : R ×_{s, U, t} R ⟶ R` correspond to `pr₀, pr₁, pr₀₂`, then
`(U, R, s, t, c)` is a groupoid in algebraic spaces over `S`. -/
@[stacks 04T4]
#check groupoid

/- Lemma 94.16.1 (5): the morphism `f` induces a canonical 1-morphism
`f_can : [U/R] ⟶ X` of stacks in groupoids over `(Sch/S)_fppf`. -/
@[stacks 04T4]
#check fCan

/- Lemma 94.16.1 (6): the 1-morphism `f_can : [U/R] ⟶ X` is fully faithful. -/
@[stacks 04T4]
#check fCan_fullyFaithful
