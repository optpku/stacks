/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.LocalCohomology.Annihilator
import StacksCheckRecall

universe u

/- Lemma 51.7.3: for finitely generated ideals `J ≤ I`, if a power of `J` annihilates
the degree-`i` local cohomology of `A` supported on `V(I)`, then a power of `J`
annihilates that of every finitely presented `A`-module which is finite locally free
after localization at each `f ∈ I`. -/
@[stacks 0BPX] #check
  (localCohomology.isAnnihilatedByPower_of_finiteLocallyFreeAway :
    ∀ {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.FinitePresentation A M] (J I : Ideal A) (hJ : J.FG) (hI : I.FG)
    (hJI : J ≤ I) (i : ℕ)
    (hA : Module.IsAnnihilatedByPower J
      ((localCohomology.withSupport I i).obj (ModuleCat.of A A)))
    (hM : ∀ f ∈ I,
      Module.FiniteLocallyFree (Localization.Away f) (LocalizedModule.Away f M)),
    Module.IsAnnihilatedByPower J
      ((localCohomology.withSupport I i).obj (ModuleCat.of A M)))
