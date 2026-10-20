/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Frobenius.Colimit

universe u

/- The chapter compatibility surface re-exports the reusable Frobenius-colimit ring API. -/
#check (Ring.FrobeniusColimit.ring :
  ∀ (p : ℕ) [Fact p.Prime] (A : Type u) [CommRing A] [Algebra (ZMod p) A],
    CommRingCat.{u})
