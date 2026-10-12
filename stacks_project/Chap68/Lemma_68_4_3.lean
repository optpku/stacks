/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap68.Lemma_68_4_3_Fibre

/-!
# Finite self-relation fibres over a point of an algebraic space

The existence of an étale scheme chart with finite self-relation fibre over a point
is equivalent to the same finiteness for every étale chart, to the existence of a
field-valued point with étale quasi-compact self-relation projections, and to the
existence of a monomorphism from the spectrum of a field in that point class.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.4.3 (1): Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let
`x` be a point of `|X|`. There exists a scheme `U`, an étale morphism
`φ : ofOver U ⟶ X`, and points `u, u'` of `U` mapping to `x` such that, setting
`R = U ×_X U`, the fibre of `|R| → |U| ×_{|X|} |U|` over `(u, u')` is finite, if and
only if the same finiteness holds for every scheme `U`, étale morphism
`φ : ofOver U ⟶ X`, and points `u, u'` of `U` mapping to `x`. -/
@[stacks 03JU]
theorem existsEtaleRelationFiniteFibre_iff_forall {S : Scheme.{u}}
    (X : AlgebraicSpace S) (x : Points X) :
    existsEtaleRelationFiniteFibre X x ↔ forallEtaleRelationFiniteFibre X x :=
  sorry

/-- Lemma 68.4.3 (2): Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let
`x` be a point of `|X|`. The self-relation fibre over `(u, u')` is finite for every
étale morphism `φ : ofOver U ⟶ X` from a scheme and all points `u, u'` mapping to
`x`, if and only if there exists a morphism `Spec(k) ⟶ X` with `k` a field in the
equivalence class of `x` such that the projections
`Spec(k) ×_X Spec(k) ⟶ Spec(k)` are étale and quasi-compact. -/
@[stacks 03JU]
theorem forallEtaleRelationFiniteFibre_iff_existsEtaleQuasiCompactFieldSelfRelation
    {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    forallEtaleRelationFiniteFibre X x ↔
      existsEtaleQuasiCompactFieldSelfRelation X x :=
  sorry

/-- Lemma 68.4.3 (3): Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let
`x` be a point of `|X|`. There exists a morphism `Spec(k) ⟶ X` with `k` a field in
the equivalence class of `x` such that the projections
`Spec(k) ×_X Spec(k) ⟶ Spec(k)` are étale and quasi-compact, if and only if there
exists a monomorphism `Spec(k) ⟶ X` with `k` a field in the equivalence class of
`x`. -/
@[stacks 03JU]
theorem existsEtaleQuasiCompactFieldSelfRelation_iff_existsMonoFieldValuedPoint
    {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) :
    existsEtaleQuasiCompactFieldSelfRelation X x ↔
      existsMonoFieldValuedPoint X x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
