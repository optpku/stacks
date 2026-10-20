/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.DividedPowers.Scheme.Pullback
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

@[expose] public section

universe u

/- Lemma 60.7.4 -/
@[stacks 07ME] #check (DividedPowerScheme.existsPullback :
  ∀ {S T T' : DividedPowerScheme.{u}}
    (f : DividedPowerScheme.Hom T S)
    (f' : DividedPowerScheme.Hom T' S),
    ∃ (T'' : DividedPowerScheme.{u})
      (g : DividedPowerScheme.Hom T'' T)
      (g' : DividedPowerScheme.Hom T'' T')
      (h : DividedPowerScheme.IsPullback g g' f f'),
      IsClosedImmersion
          (DividedPowerScheme.Pullback.baseComparison f f' g g' h) ∧
        IsIso
          (DividedPowerScheme.Pullback.zeroFiberComparison f f' g g' h))
