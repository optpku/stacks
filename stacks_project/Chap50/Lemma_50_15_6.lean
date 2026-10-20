/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.LogPole.Vanishing
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.DeRham

noncomputable section

universe u

/- Lemma 50.15.6: the first de Rham Chern class of the positive divisor line cups to zero
with every class whose restriction to the divisor vanishes. -/
@[stacks 0FMX] #check
  (AlgebraicGeometry.Scheme.DeRham.LogPole.firstChernClass_cup_eq_zero_of_restrict :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X) [IsEffectiveCartierDivisor i]
      (h_defined : RingedSpace.DeRham.LogPole.IsDefined f i) (m : ℤ) (b : cohomology f m),
      (AlgebraicGeometry.Scheme.DeRham.LogPole.restrictionOnCohomology f i m).hom b = 0 →
        (eqToHom (congrArg (cohomology f) (add_comm 2 m))).hom
          (CanonicalAction.cup f 2 m
            (AlgebraicGeometry.Scheme.DeRham.LogPole.poleLineFirstChernClass f i) b) = 0)
