/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.RationalDoublePoint
public import ReasLib.RingTheory.Gorenstein.Local
public import ReasLib.RingTheory.Normal.RationalSingularity

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 54.12.3: a two-dimensional local normal Nagata domain defining a rational
singularity, with normal completion and Gorenstein local ring, admits a finite sequence of
blowups at singular closed points ending in a regular scheme. Every post-initial stage is normal
and has finitely many singular points whose local rings satisfy the same hypotheses. -/
@[stacks 0BGE] #check (AlgebraicGeometry.Scheme.exists_singularPointBlowupSequence_regular :
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsRationalSingularity A]
    [IsNormalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
    [IsGorensteinLocalRing A],
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
                IsGorensteinLocalRing (X.presheaf.stalk x))

end AlgebraicGeometry.Scheme
