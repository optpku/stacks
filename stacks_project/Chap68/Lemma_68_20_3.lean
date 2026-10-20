/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reasonable.FiniteComponents
import StacksCheckRecall

/-!
# Getting a reasonable algebraic space from finite étale components

If every quasi-compact scheme étale over an algebraic space `X` has finitely
many irreducible components, and every codimension-`0` point of `Points X` is
represented by a monomorphism `Spec(k) ⟶ X`, then `X` is reasonable.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

/- Lemma 68.20.3: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Assume every quasi-compact scheme étale over `X` has finitely many irreducible
components, and every `x : Points X` of codimension `0` on `X` can be represented
by a monomorphism `Spec(k) ⟶ X`. Then `X` is a reasonable algebraic space.

Here a quasi-compact scheme is `CompactSpace U.left`, étale means `Etale φ`,
finitely many irreducible components means `(irreducibleComponents U.left).Finite`,
codimension `0` means `localRingDimAt x = 0`, and representation by a
monomorphism `Spec(k) ⟶ X` is `existsMonoFieldValuedPoint X x`. -/
@[stacks 0BB8] #check
  (AlgebraicGeometry.AlgebraicSpace.IsReasonable.of_finiteIrreducibleComponents_codimZero_mono :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h_components : ∀ {U : Over S} (φ : ofOver U ⟶ X),
      CompactSpace U.left → Etale φ → (irreducibleComponents U.left).Finite)
    (h_mono : ∀ x : Points X, localRingDimAt x = 0 → existsMonoFieldValuedPoint X x),
    IsReasonable X)

/- If `X` has finitely many irreducible components on compact opens and every
codimension-`0` point of `Points X` is represented by a monomorphism `Spec(k) ⟶ X`,
then `X` is reasonable. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.IsReasonable.of_hasFiniteIrreducibleComponentsOnCompactOpens :
    ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (h_mono : ∀ x : Points X, localRingDimAt x = 0 → existsMonoFieldValuedPoint X x),
    IsReasonable X)
