/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.RingTheory.Ideal.HilbertSamuel.Exact

open CategoryTheory

universe u v

/- Lemma 43.15.2: algebraic multiplicity in every degree at least the support dimension of the
middle module is additive in a short exact sequence of finite modules over a Noetherian local
ring. -/
@[stacks 0AZW] #check
  (Ideal.HilbertSamuel.ShortExact.multiplicity_eq_add :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
      {S : ShortComplex (ModuleCat.{v} R)}
      [Module.Finite R S.X₁] [Module.Finite R S.X₂] [Module.Finite R S.X₃]
      (I : Ideal R) (hI : I.IsIdealOfDefinition) (hS : S.ShortExact)
      (d : ℕ) (hd : Module.supportDim R S.X₂ ≤ d),
      Ideal.HilbertSamuel.multiplicityInDegree I S.X₂ d =
        Ideal.HilbertSamuel.multiplicityInDegree I S.X₁ d +
          Ideal.HilbertSamuel.multiplicityInDegree I S.X₃ d)
