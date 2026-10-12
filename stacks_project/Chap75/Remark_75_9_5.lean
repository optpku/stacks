/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Remark_75_9_5_AffineDiagonal
public import stacks_project.Chap75.Remark_75_9_5_InductionSets

/-!
# Choosing the collection in the qcqs spaces-étale induction lemma

Remark 75.9.5 records three standard collections `B` to which Lemma 75.9.4
applies: quasi-compact absolutely separated objects, quasi-compact objects with
affine diagonal over the terminal scheme, and the smallest collection generated
by quasi-compact opens of `X` and of affine objects of the site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Remark 75.9.5 (1): if `X` is quasi-compact and separated, the collection of
quasi-compact and separated objects of `X_spaces,étale` contains `X` and
satisfies (1), (2), and (3)(a) of Lemma 75.9.4. -/
@[stacks 08GR]
theorem qcAbsolutelySeparatedSpacesEtale_spec {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelySeparated X] :
    spacesEtaleSite.self X ∈ qcAbsolutelySeparatedSpacesEtale X ∧
      QcqsSpacesEtaleInductionSet (qcAbsolutelySeparatedSpacesEtale X) :=
  sorry

/-- Remark 75.9.5 (2): if `X` is quasi-compact with affine diagonal over the
terminal scheme, the collection of quasi-compact objects of `X_spaces,étale`
with affine diagonal over the terminal scheme contains `X` and satisfies (1),
(2), and (3)(a) of Lemma 75.9.4. -/
@[stacks 08GR]
theorem qcAbsolutelyAffineDiagonalSpacesEtale_spec {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelyAffineDiagonal X] :
    spacesEtaleSite.self X ∈ qcAbsolutelyAffineDiagonalSpacesEtale X ∧
      QcqsSpacesEtaleInductionSet (qcAbsolutelyAffineDiagonalSpacesEtale X) :=
  sorry

/-- Remark 75.9.5 (3): if `X` is quasi-compact and quasi-separated, the
smallest collection containing `X` and satisfying (1), (2), and (3)(a) of
Lemma 75.9.4 is the set of quasi-compact open subspaces of `X` and of affine
objects of `X_spaces,étale`. -/
@[stacks 08GR]
theorem qcqsGeneratedSpacesEtale_spec {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    qcqsGeneratedSpacesEtale X =
      sInf {B | spacesEtaleSite.self X ∈ B ∧ QcqsSpacesEtaleInductionSet B} :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
