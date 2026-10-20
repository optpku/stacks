/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Presentation.LichtenbaumSchlessinger

/-!
# Lichtenbaum–Schlessinger complexes of polynomial presentations
-/

universe u

#check (Algebra.Presentation.LichtenbaumSchlessinger.complex :
  ∀ {R S ι σ : Type u} [CommRing R] [CommRing S] [Algebra R S],
    Algebra.Presentation R S ι σ → CochainComplex (ModuleCat.{u} S) ℤ)
