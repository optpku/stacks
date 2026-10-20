/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Projective
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 30.24.3: coherent completion along `I 𝒪_X` is an equivalence for a projective
morphism over an `I`-adically complete Noetherian ring. -/
@[stacks 0885] #check
  (@AlgebraicGeometry.Scheme.CoherentCompletion.functor_isEquivalence_of_projective :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {X : Scheme.{u}} [IsNoetherian X]
      (I : Ideal A) [IsAdicComplete I A]
      (f : X ⟶ Spec (CommRingCat.of A)) [AlgebraicGeometry.Projective f],
      (AlgebraicGeometry.Scheme.CoherentCompletion.functor
        ((AlgebraicGeometry.Scheme.idealSheafDataOfIdealOnSpec I).comap f)).IsEquivalence)
