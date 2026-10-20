/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.FullyFaithful
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 30.24.1: if `A` is Noetherian and `I`-adically complete, `f : X ⟶ Spec(A)` is
proper, and `𝓘 = I 𝒪_X`, then the coherent-completion functor `Coh(𝒪_X) ⥤ Coh(X, 𝓘)` is
fully faithful. -/
@[stacks 0883] #check
  (AlgebraicGeometry.Scheme.CoherentCompletion.fullyFaithful_of_isProper :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {X : Scheme.{u}} [IsNoetherian X]
      (I : Ideal A) [IsAdicComplete I A]
      (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f],
      Nonempty (AlgebraicGeometry.Scheme.CoherentCompletion.functor
        ((AlgebraicGeometry.Scheme.idealSheafDataOfIdealOnSpec I).comap f)).FullyFaithful)
