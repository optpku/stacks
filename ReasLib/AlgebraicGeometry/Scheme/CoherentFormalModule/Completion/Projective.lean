/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.AdicCompletion.Basic
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentCompletion

/-- For a projective morphism to the spectrum of an `I`-adically complete Noetherian ring,
coherent completion along `I 𝒪_X` is an equivalence of categories. -/
@[stacks 0885, instance]
instance functor_isEquivalence_of_projective
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} [IsNoetherian X]
    (I : Ideal A) [IsAdicComplete I A]
    (f : X ⟶ Spec (CommRingCat.of A)) [AlgebraicGeometry.Projective f] :
    (functor ((idealSheafDataOfIdealOnSpec I).comap f)).IsEquivalence :=
  sorry

end AlgebraicGeometry.Scheme.CoherentCompletion
