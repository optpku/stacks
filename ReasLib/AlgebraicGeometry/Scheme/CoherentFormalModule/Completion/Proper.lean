/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentCompletion

/-- For a proper morphism to the spectrum of an `I`-adically complete Noetherian ring,
coherent completion along `I 𝒪_X` is an equivalence of categories. -/
@[stacks 088C, instance]
instance functor_isEquivalence_of_isProper
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} [IsNoetherian X]
    (I : Ideal A) [IsAdicComplete I A]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] :
    (functor ((idealSheafDataOfIdealOnSpec I).comap f)).IsEquivalence :=
  sorry

end AlgebraicGeometry.Scheme.CoherentCompletion
