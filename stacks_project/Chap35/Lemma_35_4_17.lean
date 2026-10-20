/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Descent.SplitCoequalizer
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.4.17: for a module descent datum `(M, θ)` over `S/R`, applying character
duality to the displayed descent equalizer gives a split coequalizer. -/
@[stacks 08X1] #check (@ModuleCat.DescentData.SplitCoequalizer.splitting :
  {R S : Type u} →
    [CommRing R] → [CommRing S] → [Algebra R S] →
      (D : ModuleCat.DescentData (algebraMap R S)) →
        CategoryTheory.IsSplitCoequalizer
          (CharacterModule.dualAddMap
            (ModuleCat.DescentData.SplitEqualizer.upper D))
          (CharacterModule.dualAddMap
            (ModuleCat.DescentData.SplitEqualizer.lower D))
          (CharacterModule.dualAddMap
            (ModuleCat.DescentData.SplitEqualizer.source D)))
