/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.AdicCompletion.Exactness.Counterexample

@[expose] public section

universe u

open CategoryTheory

/- Lemma 110.9.1 (1): `I`-adic completion is not an exact functor in general:
there exists a short exact sequence of `R`-modules whose objectwise `I`-adic
completion is not exact. -/
@[stacks 05JG] #check (AdicCompletion.Counterexample.exists_shortExact_map_not_exact :
    ∃ (R : Type u) (_ : CommRing R) (I : Ideal R) (S : ShortComplex (ModuleCat.{u} R)),
      S.ShortExact ∧ ¬ (AdicCompletion.mapShortComplex I S).Exact)

/- Lemma 110.9.1 (2): `I`-adic completion is not even right exact in general,
even when `I` is finitely generated, on the category of finitely presented modules. -/
@[stacks 05JG] #check (AdicCompletion.Counterexample.exists_fg_finitePresentation_not_rightExact :
    ∃ (R : Type u) (_ : CommRing R) (I : Ideal R) (S : ShortComplex (ModuleCat.{u} R)),
      I.FG ∧ Module.FinitePresentation R S.X₁ ∧ Module.FinitePresentation R S.X₂ ∧
        Module.FinitePresentation R S.X₃ ∧ S.Exact ∧ Epi S.g ∧
        ¬ (AdicCompletion.mapShortComplex I S).Exact)
