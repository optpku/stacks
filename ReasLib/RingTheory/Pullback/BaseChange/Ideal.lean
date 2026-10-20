/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Maps
public import ReasLib.RingTheory.Pullback.BaseChange
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ideals in a fibre-product base change

@stack 08KN
-/

@[expose] public section

universe u

noncomputable section

variable {B A A' Dp : Type u}
variable [CommRing B] [CommRing A] [CommRing A'] [CommRing Dp]

namespace FiberProductBaseChangeSituation

local notation "Situation" => @FiberProductBaseChangeSituation B A A' Dp _ _ _ _

/-- Lemma 15.7.3: the image in `C'` of the extension to `D'` of `ker(B' → B)` is the
extension of `ker(A' → A)`. -/
@[stacks 08KN "extended kernel ideal under tensor base change"]
theorem map_map_ker_bprimeToB_eq_map_ker_fromAprime (S : Situation) :
    Ideal.map S.dprimeToCPrime (Ideal.map S.bprimeToDp (RingHom.ker S.bprimeToB)) =
      Ideal.map S.aprimeToCPrime (RingHom.ker S.fromAprime) := sorry

end FiberProductBaseChangeSituation
