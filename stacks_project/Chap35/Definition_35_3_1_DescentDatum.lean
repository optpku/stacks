/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.DescentDatum

@[expose] public section

universe u v w

/- Compatibility bridge for the module descent datum API. -/
#check (@Module.DescentDatum :
  (R : Type u) → (A : Type v) → (N : Type w) →
    [CommRing R] → [CommRing A] → [Algebra R A] →
      [AddCommGroup N] → [Module R N] → [Module A N] →
        [IsScalarTower R A N] → [SMulCommClass R A N] → Type (max v w))
