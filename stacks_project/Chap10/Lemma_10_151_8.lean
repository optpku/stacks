/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.Unramified
import StacksCheckRecall

/-! @stack 08WD -/

@[expose] public section

universe u v

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- Lemma 10.151.8: etaleness, flat G-unramifiedness, and flat unramifiedness
of finite presentation are equivalent. -/
@[stacks 08WD]
#check (Etale.tfae_flat_gUnramified (R := R) (S := S) :
  List.TFAE
    [ Etale R S
    , Module.Flat R S ∧ GUnramified R S
    , Module.Flat R S ∧ Unramified R S ∧ FinitePresentation R S
    ])

#check (Etale.iff_flat_and_gUnramified (R := R) (S := S) :
  Etale R S ↔ Module.Flat R S ∧ GUnramified R S)

#check (Etale.iff_flat_and_unramified_and_finitePresentation (R := R) (S := S) :
  Etale R S ↔ Module.Flat R S ∧ Unramified R S ∧ FinitePresentation R S)

end Algebra
