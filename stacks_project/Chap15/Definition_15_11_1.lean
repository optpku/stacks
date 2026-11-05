/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Henselian.Factorization
import StacksCheckRecall

/-!
# Definition 15.11.1

@stack 09XE
-/

@[expose] public section

open Polynomial

universe u

namespace Ideal

variable {A : Type u} [CommRing A]
variable (I : Ideal A) [HenselianRing A I]

-- Definition 15.11.1 (09XE): the canonical owner for a henselian pair `(A, I)` is
-- `HenselianRing A I`.
@[stacks 09XE "Definition 15.11.1 (1)"]
#check (HenselianRing A I : Prop)

-- Definition 15.11.1 (1): the ideal of a henselian pair lies in `Ring.jacobson A`.
@[stacks 09XE "Definition 15.11.1 (1)"]
#check
  (le_ring_jacobson_of_henselianRing (A := A) I :
    I ≤ Ring.jacobson A)

-- Definition 15.11.1 (2): monic coprime factorizations modulo the henselian ideal lift to
-- monic factorizations over `A`.
@[stacks 09XE]
#check
  (exists_monic_coprime_factorization_lift (A := A) I :
    (f : A[X]) → f.Monic →
      (g₀ h₀ : (A ⧸ I)[X]) → g₀.Monic → h₀.Monic → IsCoprime g₀ h₀ →
        f.map (Ideal.Quotient.mk I) = g₀ * h₀ →
          ∃ g h : A[X],
            g.Monic ∧ h.Monic ∧ f = g * h ∧
              g.map (Ideal.Quotient.mk I) = g₀ ∧
                h.map (Ideal.Quotient.mk I) = h₀)

end Ideal
