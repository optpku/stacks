/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reasonable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteComponents
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.RelationFiniteFibre

/-!
# Reasonableness from finite irreducible components

An algebraic space is reasonable if its quasi-compact étale scheme charts have
finitely many irreducible components and its codimension-zero points admit
monomorphic field-valued representatives.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsReasonable

/-- An algebraic space is reasonable if every quasi-compact scheme étale over it
has finitely many irreducible components and every codimension-zero point is
represented by a monomorphism from the spectrum of a field. -/
@[stacks 0BB8]
theorem of_finiteIrreducibleComponents_codimZero_mono
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h_components : ∀ {U : Over S} (φ : ofOver U ⟶ X),
      CompactSpace U.left → Etale φ → (irreducibleComponents U.left).Finite)
    (h_mono : ∀ x : Points X, localRingDimAt x = 0 → existsMonoFieldValuedPoint X x) :
    IsReasonable X := sorry

/-- If `X` has finitely many irreducible components on compact opens and every
codimension-zero point is represented by a monomorphism from the spectrum of a
field, then `X` is reasonable. -/
theorem of_hasFiniteIrreducibleComponentsOnCompactOpens
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (h_mono : ∀ x : Points X, localRingDimAt x = 0 → existsMonoFieldValuedPoint X x) :
    IsReasonable X := sorry

end IsReasonable

end AlgebraicGeometry.AlgebraicSpace
