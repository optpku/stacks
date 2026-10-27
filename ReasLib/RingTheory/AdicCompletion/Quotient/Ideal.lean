/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.Quotient
public import ReasLib.RingTheory.AdicCompletion.Congruence

@[expose] public section

universe u

namespace AdicCompletion

/-- An ideal containing a power of a finitely generated adic ideal extends to the
kernel of the canonical map from the completion to its quotient. -/
theorem map_eq_ker_toQuotient {B : Type u} [CommRing B]
    (K J : Ideal B) (hK : K.FG) (N : ℕ) (hN : K ^ N ≤ J) :
    Ideal.map (algebraMap B (AdicCompletion K B)) J =
      RingHom.ker (AdicCompletion.toQuotient K J N hN) := sorry

end AdicCompletion
