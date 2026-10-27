/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Basic

@[expose] public section

universe u

namespace RingCat

/-- A bundled ring with commutative multiplication is a commutative ring,
retaining its canonical ring operations. -/
instance (priority := 50) commRingOfMulComm (R : RingCat.{u})
    [h : Fact (∀ a b : R, a * b = b * a)] : CommRing R where
  toRing := inferInstance
  mul_comm := h.elim

end RingCat
