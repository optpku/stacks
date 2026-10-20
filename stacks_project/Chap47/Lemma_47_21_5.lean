/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.RingTheory.Gorenstein.ResidueFieldExt
import StacksCheckRecall

universe u

open CategoryTheory
open scoped DerivedExt

/- Lemma 47.21.5: A Noetherian local ring `A` is Gorenstein if and only if
the derived Ext groups from its residue field to `A` are subsingleton in all sufficiently large
integer degrees. -/
@[stacks 0BJI] #check
  (IsGorensteinLocalRing.iff_eventually_residueField_ext :
    (A : Type u) → [CommRing A] → [IsLocalRing A] → [IsNoetherianRing A] →
      IsGorensteinLocalRing A ↔
        ∃ b : ℤ, ∀ i : ℤ, b < i →
          Subsingleton
            (Ext⁽i⁾((DerivedCategory.singleFunctor (ModuleCat A) 0).obj
              (ModuleCat.of A (IsLocalRing.ResidueField A)),
              (DerivedCategory.singleFunctor (ModuleCat A) 0).obj (ModuleCat.of A A))))
