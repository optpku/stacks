/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_49_1_FiniteComponents
public import stacks_project.Chap68.Lemma_68_4_3_Fibre
public import stacks_project.Chap68.Lemma_68_17_4_Relative

/-!
# Getting a reasonable algebraic space from finite étale components

If every quasi-compact scheme étale over an algebraic space `X` has finitely
many irreducible components, and every codimension-`0` point of `Points X` is
represented by a monomorphism `Spec(k) ⟶ X`, then `X` is reasonable.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsReasonable

/-- Lemma 68.20.3: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Assume every quasi-compact scheme étale over `X` has finitely many irreducible
components, and every `x : Points X` of codimension `0` on `X` can be represented
by a monomorphism `Spec(k) ⟶ X`. Then `X` is a reasonable algebraic space.

Here a quasi-compact scheme is `CompactSpace U.left`, étale means `Etale φ`,
finitely many irreducible components means `(irreducibleComponents U.left).Finite`,
codimension `0` means `localRingDimAt x = 0`, and representation by a
monomorphism `Spec(k) ⟶ X` is `existsMonoFieldValuedPoint X x`. -/
@[stacks 0BB8]
theorem of_finiteIrreducibleComponents_codimZero_mono
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h_components : ∀ {U : Over S} (φ : ofOver U ⟶ X),
      CompactSpace U.left → Etale φ → (irreducibleComponents U.left).Finite)
    (h_mono : ∀ x : Points X, localRingDimAt x = 0 → existsMonoFieldValuedPoint X x) :
    IsReasonable X := sorry

/-- If `X` has finitely many irreducible components on compact opens and every
codimension-`0` point of `Points X` is represented by a monomorphism `Spec(k) ⟶ X`,
then `X` is reasonable. -/
theorem of_hasFiniteIrreducibleComponentsOnCompactOpens
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (h_mono : ∀ x : Points X, localRingDimAt x = 0 → existsMonoFieldValuedPoint X x) :
    IsReasonable X := sorry

end IsReasonable

end AlgebraicGeometry.AlgebraicSpace
