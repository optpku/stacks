/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.CohomologicalDimension
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.SetTheory.Cardinal.ENat

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K]
variable [HasSheafify (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{u})]
variable {L : Type u} [Field L] [Algebra K L]
variable [HasSheafify (Spec (CommRingCat.of L)).smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Spec (CommRingCat.of L)).smallEtaleTopology AddCommGrpCat.{u})]

/-- For a field extension, locally torsion étale sheaf cohomology vanishes above
the cohomological dimension of the base field plus the transcendence degree.
Infinite transcendence degree is interpreted as `⊤`. -/
theorem cohomologicalDimensionBound_add_trdeg :
    cohomologicalDimensionBound (Spec (CommRingCat.of L))
      (cohomologicalDimension (Spec (CommRingCat.of K)) +
        id (α := WithTop ℕ) (Cardinal.toENat (Algebra.trdeg K L))) := sorry

/-- The cohomological dimension of a field extension is at most the
cohomological dimension of the base field plus the transcendence degree.
Infinite transcendence degree is interpreted as `⊤`. -/
theorem cohomologicalDimension_le_add_trdeg :
    cohomologicalDimension (Spec (CommRingCat.of L)) ≤
      cohomologicalDimension (Spec (CommRingCat.of K)) +
        id (α := WithTop ℕ) (Cardinal.toENat (Algebra.trdeg K L)) := by
  exact cohomologicalDimension_le_of_bound (Spec (CommRingCat.of L))
    (cohomologicalDimension (Spec (CommRingCat.of K)) +
      id (α := WithTop ℕ) (Cardinal.toENat (Algebra.trdeg K L)))
    cohomologicalDimensionBound_add_trdeg

end AlgebraicGeometry.Scheme

end
