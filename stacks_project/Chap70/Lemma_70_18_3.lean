/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap70.Lemma_70_18_3_Neighborhood
public import stacks_project.Chap70.Lemma_70_18_3_StalkGluing

/-!
# Glueing algebraic spaces of finite presentation near a point

For a retrocompact open `U ⊆ S` and a point `s` in the complement of `U`, the
2-colimit of algebraic spaces of finite presentation over open neighborhoods of
`s` containing `U` is equivalent to the 2-fibre product of those over `U` and
over `Spec(𝒪_{S,s})`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver
open OpenNeighborhood

/-- Lemma 70.18.3: Let `S` be a scheme. Let `U ⊆ S` be a retrocompact open. Let
`s ∈ S` be a point in the complement of `U`. With `V = Spec(𝒪_{S,s}) ∩ U` there
is an equivalence of categories
`colim_{s ∈ U' ⊃ U open} FP_{U'} ⥤ FP_U ×_{FP_V} FP_{Spec(𝒪_{S,s})}`, where
`FP_T` is the category of algebraic spaces of finite presentation over `T`.
Here `V` is `stalkOpenIntersection S U s`, retrocompactness of `U` is
`QuasiCompact U.ι`, and the comparison functor is `comparison`. -/
@[stacks 0E91]
theorem comparison_isEquivalence (S : Scheme.{u}) (U : S.Opens)
    [AlgebraicGeometry.QuasiCompact U.ι] (s : S) (hsU : s ∉ (U : Set S)) :
    (comparison S U s).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FinitePresentationOver
