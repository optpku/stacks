/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.TorsionFree
import StacksCheckRecall

/-!
# Lemma 15.22.9

@stack 0538
-/

universe u v

/- Lemma 15.22.9 (0538): every flat module over a domain is torsion-free. -/
@[stacks 0538]
#check fun {R : Type u} {M : Type v} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Flat R M] ↦
  (inferInstance : Module.IsTorsionFree R M)

#check @Module.Flat.isTorsionFree
