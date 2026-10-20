/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Descent.SplitEqualizer

@[expose] public section

noncomputable section

universe u

open CategoryTheory

/- The explicit tensor-multiplication splitting of the additive descent equalizer. -/
#check (@ModuleCat.DescentData.SplitEqualizer.splitting :
  {R S : Type u} →
    [CommRing R] → [CommRing S] → [Algebra R S] →
      (D : ModuleCat.DescentData (algebraMap R S)) →
        CategoryTheory.IsSplitEqualizer
          (ModuleCat.DescentData.SplitEqualizer.upper D)
          (ModuleCat.DescentData.SplitEqualizer.lower D)
          (ModuleCat.DescentData.SplitEqualizer.source D))
