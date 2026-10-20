/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.RingTheory.Ideal.RegularProduct.LocalPrincipal

universe u

/- Exercise 111.60.7: in a local ring, if a regular element generates the product of two
ideals, then the first ideal is principal. -/
@[stacks 0EER] #check (Ideal.isPrincipal_of_mul_eq_span_singleton_regular :
  ∀ {R : Type u} [CommRing R] [IsLocalRing R] (I J : Ideal R) (f : R),
    IsRegular f → I * J = Ideal.span ({f} : Set R) → I.IsPrincipal)
