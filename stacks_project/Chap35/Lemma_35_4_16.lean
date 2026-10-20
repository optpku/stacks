/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Descent.SplitEqualizer
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open CategoryTheory

/- Lemma 35.4.16: for a module descent datum `(M, θ)` over `S/R`, the diagram
`M ⟶ M ⊗_S S₂ ⇉ M ⊗_S S₃` is a split equalizer. -/
@[stacks 08WZ] #check (@ModuleCat.DescentData.SplitEqualizer.splitting :
  {R S : Type u} →
    [CommRing R] → [CommRing S] → [Algebra R S] →
      (D : ModuleCat.DescentData (algebraMap R S)) →
        CategoryTheory.IsSplitEqualizer
          (ModuleCat.DescentData.SplitEqualizer.upper D)
          (ModuleCat.DescentData.SplitEqualizer.lower D)
          (ModuleCat.DescentData.SplitEqualizer.source D))
