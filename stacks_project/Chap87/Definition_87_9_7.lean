/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Lemma_87_10_3_Types
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Definition 87.9.7 (1): for a scheme `S` and an affine formal algebraic space
`X` over `S`, we say `X` is McQuillan if `X` satisfies the equivalent
conditions of Lemma 87.9.6. -/
@[stacks 0AID] #check IsMcQuillan

/- Definition 87.9.7 (2): writing `A` for the weakly admissible topological ring
associated to `X`, we say `X` is classical if `X` is McQuillan and `A` is
admissible. -/
@[stacks 0AID] #check IsClassicalAffine

/- Definition 87.9.7 (3): writing `A` for the weakly admissible topological ring
associated to `X`, we say `X` is weakly adic if `X` is McQuillan and `A` is
weakly adic. -/
@[stacks 0AID] #check IsWeaklyAdicAffine

/- Definition 87.9.7 (4): writing `A` for the weakly admissible topological ring
associated to `X`, we say `X` is adic if `X` is McQuillan and `A` is adic. -/
@[stacks 0AID] #check IsAdicAffine

/- Definition 87.9.7 (5): writing `A` for the weakly admissible topological ring
associated to `X`, we say `X` is adic* if `X` is McQuillan, `A` is adic, and
`A` has a finitely generated ideal of definition. -/
@[stacks 0AID] #check IsAdicStar

/- Definition 87.9.7 (6): writing `A` for the weakly admissible topological ring
associated to `X`, we say `X` is Noetherian if `X` is McQuillan and `A` is
both Noetherian and adic. -/
@[stacks 0AID] #check IsNoetherianAffine
