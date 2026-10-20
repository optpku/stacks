/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.FiniteType.FaithfullyFlat
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 35.14.2: finite type descends from a composite along a faithfully flat,
finitely presented second map. -/
@[stacks 0367] #check
  (RingHom.FiniteType.of_comp_of_faithfullyFlat_of_finitePresentation :
    ∀ {R : Type u} {A : Type v} {B : Type w}
      [CommRing R] [CommRing A] [CommRing B]
      {f : R →+* A} {g : A →+* B},
      (g.comp f).FiniteType → g.FaithfullyFlat → g.FinitePresentation → f.FiniteType)
