/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex

@[expose] public section

/-!
# Restriction of scalars for naive cotangent complexes

@stack 07BN

This leaf gives the canonical change-of-coefficients view of the two-term
naive cotangent complex of an algebra presentation.  It depends only on the
presentation-level complex and on `ModuleCat.restrictScalars`.
-/

open CategoryTheory

universe u v w x

noncomputable section

namespace Algebra.Extension.NaiveCotangent

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- The naive cotangent complex of a presentation, viewed over
an arbitrary coefficient ring along an explicit ring homomorphism. -/
@[stacks 07BN "restriction along a ring homomorphism for naive cotangent complexes"]
noncomputable abbrev restrictScalarsAlong
    (P : Extension.{w} A B) {R : Type x} [CommRing R] (f : R →+* B) :
    ChainComplex (ModuleCat.{max v w} R) ℕ :=
  ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (complex P)

/-- The naive cotangent complex of a
presentation, viewed over a smaller coefficient ring by restriction of
scalars. -/
@[stacks 07BN "restriction of scalars for naive cotangent complexes"]
noncomputable abbrev restrictScalars
    (P : Extension.{w} A B) (R : Type x) [CommRing R] [Algebra R B] :
    ChainComplex (ModuleCat.{max v w} R) ℕ :=
  restrictScalarsAlong P (algebraMap R B)

/-- The differentials above degree one vanish after restricting scalars along any ring
homomorphism on a naive cotangent complex. -/
@[simp, stacks 07BN]
theorem restrictScalarsAlong_d_succ_succ
    (P : Extension.{w} A B) {R : Type x} [CommRing R] (f : R →+* B) (n : ℕ) :
    (restrictScalarsAlong P f).d (n + 2) (n + 1) = 0 := sorry

/-- The differentials above degree one vanish after restricting scalars on a
naive cotangent complex. -/
@[simp, stacks 07BN]
theorem restrictScalars_d_succ_succ
    (P : Extension.{w} A B) (R : Type x) [CommRing R] [Algebra R B] (n : ℕ) :
    (restrictScalars P R).d (n + 2) (n + 1) = 0 := sorry

end Algebra.Extension.NaiveCotangent

namespace NaiveCotangent

/-- Notation for the canonical naive cotangent complex, viewed over a smaller
coefficient ring by restriction of scalars. -/
scoped notation:max "NL{" S "⁄" R "}↾[" T "]" =>
  Algebra.Extension.NaiveCotangent.restrictScalars
    (Algebra.Generators.toExtension (Algebra.Generators.self R S)) T

end NaiveCotangent
