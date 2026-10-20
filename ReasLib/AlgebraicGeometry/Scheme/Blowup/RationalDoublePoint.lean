/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.SingularPointSequence
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.RingTheory.Gorenstein.Local
public import ReasLib.RingTheory.Normal.RationalSingularity

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A rational double point admits a finite singular-point blowup sequence ending in a regular
scheme, with every post-initial stage preserving the corresponding singularity conditions. -/
theorem exists_singularPointBlowupSequence_regular
    (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    [IsNormalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
    [IsGorensteinLocalRing A] :
    ∃ (Y : Scheme.{u}) (s : SingularPointBlowupSequence (Spec (.of A)) Y),
      Regular Y ∧
        s.EveryTarget fun X ↦
          X.isNormal ∧ (Sing(X)).Finite ∧
            ∀ x : X, x ∈ Sing(X) →
              IsDomain (X.presheaf.stalk x) ∧
                IsRationalSingularity (X.presheaf.stalk x) ∧
                IsNormalRing
                  (AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
                    (X.presheaf.stalk x)) ∧
                IsGorensteinLocalRing (X.presheaf.stalk x) := sorry

end AlgebraicGeometry.Scheme
