/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SurjectiveDescent
import StacksCheckRecall

/-!
# Lemma 81.4.5

A morphism of algebraic spaces that is surjective integral, surjective proper,
or surjective flat and locally of finite presentation satisfies descent for
Type-valued sheaves on the small étale site.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 81.4.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. If `f` is either surjective and integral, surjective and proper,
or surjective and flat and locally of finite presentation, then the functor from
Type-valued sheaves on the small étale site of `Y` to singleton descent data
along `{f}` is an equivalence of categories. -/
@[stacks 0GFW] #check
  (AlgebraicGeometry.AlgebraicSpace.EtaleSheaf.descentIsEquivalenceOfSurjective :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Surjective f],
      IsIntegralHom f ∨ Proper f ∨ (Flat f ∧ LocallyOfFinitePresentation f) →
        (AlgebraicGeometry.AlgebraicSpace.EtaleSheaf.pseudofunctor.toDescentData
          (fun _ : PUnit ↦ f)).IsEquivalence)

#check
  (AlgebraicGeometry.AlgebraicSpace.EtaleSheaf.descentIsEquivalenceOfSurjectiveIntegral :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Surjective f] [IsIntegralHom f],
      (AlgebraicGeometry.AlgebraicSpace.EtaleSheaf.pseudofunctor.toDescentData
        (fun _ : PUnit ↦ f)).IsEquivalence)

#check
  (AlgebraicGeometry.AlgebraicSpace.EtaleSheaf.descentIsEquivalenceOfSurjectiveProper :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Surjective f] [Proper f],
      (AlgebraicGeometry.AlgebraicSpace.EtaleSheaf.pseudofunctor.toDescentData
        (fun _ : PUnit ↦ f)).IsEquivalence)

#check
  (AlgebraicGeometry.AlgebraicSpace.EtaleSheaf.descentIsEquivalenceOfSurjectiveFlat :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Surjective f] [Flat f] [LocallyOfFinitePresentation f],
      (AlgebraicGeometry.AlgebraicSpace.EtaleSheaf.pseudofunctor.toDescentData
        (fun _ : PUnit ↦ f)).IsEquivalence)
