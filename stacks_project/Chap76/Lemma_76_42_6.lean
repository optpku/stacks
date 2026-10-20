/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoherentFormalModule.Completion.ProperSupport

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology

universe u

/- Lemma 76.42.6 (1): over a Noetherian I-adically complete ring A, completion
on a finite-type separated algebraic space is bijective on morphisms of coherent
modules whose supports have proper intersection over Spec A. -/
@[stacks 08B9] #check (AlgebraicGeometry.AlgebraicSpace.CoherentCompletion.homMap_bijective :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [FiniteType (SchemeRealization.toBase X)] [Separated (SchemeRealization.toBase X)],
    ∀ (ℱ 𝒢 : Coh X),
      ClosedSubset.ProperOver (SchemeRealization.toBase X)
        (closedSupport ℱ.obj ⊓ closedSupport 𝒢.obj) →
      Function.Bijective (fun f : ℱ ⟶ 𝒢 ↦
        (CoherentCompletion.functor (pullbackIdeal I (SchemeRealization.toBase X))).map f))

/- Lemma 76.42.6 (2): the completion functor restricted to coherent modules
with proper support over Spec A is full. -/
@[stacks 08B9] #check (AlgebraicGeometry.AlgebraicSpace.Modules.instFull_coherentProperSupportCompletionFunctor :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [FiniteType (SchemeRealization.toBase X)] [Separated (SchemeRealization.toBase X)],
    (coherentProperSupportCompletionFunctor (SchemeRealization.toBase X)
      (pullbackIdeal I (SchemeRealization.toBase X))).Full)

/- Lemma 76.42.6 (3): the completion functor restricted to coherent modules
with proper support over Spec A is faithful. -/
@[stacks 08B9] #check (AlgebraicGeometry.AlgebraicSpace.Modules.instFaithful_coherentProperSupportCompletionFunctor :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [FiniteType (SchemeRealization.toBase X)] [Separated (SchemeRealization.toBase X)],
    (coherentProperSupportCompletionFunctor (SchemeRealization.toBase X)
      (pullbackIdeal I (SchemeRealization.toBase X))).Faithful)
