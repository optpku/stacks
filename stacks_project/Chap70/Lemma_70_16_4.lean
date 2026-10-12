/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Lemma_70_16_4_Filtration

/-!
# Finite closed filtrations of qcqs algebraic spaces by scheme covers

A quasi-compact quasi-separated algebraic space admits a finite nested closed
filtration of finite presentation, beginning with a thickening and ending empty,
together with surjective finite finitely presented scheme covers that are finite
étale over successive differences.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 70.16.4: Let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S`. There exist `t ≥ 0` and nested closed
subspaces `X ⊃ Z₀ ⊃ ⋯ ⊃ Z_t = ∅` such that each `Z_i ⟶ X` is of finite
presentation, `Z₀ ⊂ X` is a thickening, and for each `i < t` there is a scheme
`Y_i` and a surjective finite finitely presented morphism `Y_i ⟶ Z_i` which is
finite étale over `Z_i \ Z_{i+1}`. -/
@[stacks 0GUP]
theorem exists_finiteClosedSchemeCoverFiltration {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    Nonempty (FiniteClosedSchemeCoverFiltration X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
