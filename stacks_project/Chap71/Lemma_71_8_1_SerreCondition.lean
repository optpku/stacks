/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_7_2
public import stacks_project.Chap66.Remark_66_7_3_EtaleLocal

/-!
# Serre conditions on algebraic spaces

An algebraic space satisfies `(S_k)` when it has the étale-local scheme property of
being locally Noetherian and satisfying `(S_k)`, in the sense of Properties of
Spaces, Definition 66.7.2.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space satisfies `(S_k)` when it has the étale-local type-property of
being locally Noetherian and satisfying the scheme-theoretic Serre condition
`(S_k)`. -/
def satisfiesSerreConditionS {S : Scheme.{u}} (X : AlgebraicSpace S) (k : ℕ) : Prop :=
  hasEtaleLocal
    (fun U : Scheme.{u} ↦
      AlgebraicGeometry.IsLocallyNoetherian U ∧ Scheme.satisfiesSerreConditionS U k)
    X

/-- `satisfiesSerreConditionS X k` is the étale-local type-property of being locally
Noetherian and satisfying the scheme-theoretic condition `(S_k)`. -/
theorem satisfiesSerreConditionS_def {S : Scheme.{u}} (X : AlgebraicSpace S)
    (k : ℕ) :
    satisfiesSerreConditionS X k ↔
      hasEtaleLocal
        (fun U : Scheme.{u} ↦
          AlgebraicGeometry.IsLocallyNoetherian U ∧ Scheme.satisfiesSerreConditionS U k)
        X :=
  sorry

/-- An algebraic space satisfies `(S_k)` if and only if every étale morphism from a
scheme to it has locally Noetherian source satisfying `(S_k)`. -/
theorem satisfiesSerreConditionS_iff_forallEtale {S : Scheme.{u}}
    (X : AlgebraicSpace S) (k : ℕ) :
    satisfiesSerreConditionS X k ↔
      forallEtale
        (fun U : Scheme.{u} ↦
          AlgebraicGeometry.IsLocallyNoetherian U ∧ Scheme.satisfiesSerreConditionS U k)
        X :=
  sorry

/-- A locally Noetherian scheme over `S`, viewed as an algebraic space, satisfies
`(S_k)` if and only if the scheme itself satisfies `(S_k)`. -/
theorem satisfiesSerreConditionS_ofOver {S : Scheme.{u}} (T : Over S)
    [AlgebraicGeometry.IsLocallyNoetherian T.left] (k : ℕ) :
    satisfiesSerreConditionS (ofOver T) k ↔ T.left.satisfiesSerreConditionS k :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
