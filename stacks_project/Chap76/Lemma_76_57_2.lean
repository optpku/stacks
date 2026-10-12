/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_57_2_Filtration

/-!
# Finite closed filtrations of qcqs algebraic spaces by resolution blowups

A quasi-compact quasi-separated algebraic space admits a finite nested closed
filtration of finite presentation, beginning with a thickening and ending empty,
together with admissible blowups of the successive differences that have the
resolution property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.57.2: Let `S` be a scheme. Let `X` be a quasi-compact and
quasi-separated algebraic space over `S`. There exist `t ≥ 0` and nested closed
subspaces `X ⊃ Z₀ ⊃ ⋯ ⊃ Z_t = ∅` such that each `Z_i ⟶ X` is of finite
presentation, `Z₀ ⊂ X` is a thickening, and for each `i < t` there is a
`(Z_i \ Z_{i+1})`-admissible blowing up `Z'_i ⟶ Z_i` such that `Z'_i` has
the resolution property. -/
@[stacks 0GV6]
theorem exists_finiteClosedResolutionBlowupFiltration {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    Nonempty (FiniteClosedResolutionBlowupFiltration X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
