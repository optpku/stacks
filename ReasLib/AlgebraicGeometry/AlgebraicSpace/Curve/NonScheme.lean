/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.Operations
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProper

/-!
# Families of curves with nonschematic total space

There are proper, flat, finitely presented families of curves of relative
dimension at most one whose total algebraic space is not a scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- There exists a field `k`, an algebraic space over the affine line over
`Spec k`, and a proper, flat, finitely presented morphism of relative dimension
at most one whose source is not a scheme. -/
theorem exists_familyOfCurves_affineLine_not_isScheme :
    ∃ (k : Type u) (_ : Field k)
      (X : AlgebraicSpace (Spec (CommRingCat.of k)))
      (f : X ⟶ affineLine (Spec (CommRingCat.of k))),
      FpFlatProper f ∧ RelativeDimensionLE f 1 ∧ ¬ IsScheme X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
