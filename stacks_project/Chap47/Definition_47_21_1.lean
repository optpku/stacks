/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Gorenstein.Ring
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 47.21.1 (1): A Noetherian local ring is Gorenstein when its degree-zero
complex is dualizing. This is represented by the equivalent canonical local-ring property. -/
@[stacks 0DW7] #check
  (IsGorensteinLocalRing :
    (R : Type u) → [CommRing R] → [IsLocalRing R] → Prop)

/- Definition 47.21.1 (2): A Noetherian commutative ring is Gorenstein when its localization
at every prime ideal is a Gorenstein local ring. -/
@[stacks 0DW7] #check
  (IsGorensteinRing :
    (R : Type u) → [CommRing R] → Prop)
