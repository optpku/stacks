/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import stacks_project.Chap83.Definition_83_5_13_SetTheoretic
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PreRelation

universe u

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U)

/- Definition 83.5.13 (1): a pre-relation `j : R ⟶ U ⨯ U` over `B` is a set-theoretic
pre-equivalence relation if for every algebraically closed field `k` over `B` the
relation `~_R` on `U(k)` given by a field extension `K/k` and `r ∈ R(K)` with
`s(r) = ū` and `t(r) = ū'` is an equivalence relation. -/
@[stacks 0490] #check (IsSetTheoreticPreEquivalence P : Prop)

/- Definition 83.5.13 (2): a pre-relation `j : R ⟶ U ⨯ U` over `B` is a set-theoretic
equivalence relation if `j` is universally injective and a set-theoretic
pre-equivalence relation. -/
@[stacks 0490] #check (IsSetTheoreticEquivalence P : Prop)
