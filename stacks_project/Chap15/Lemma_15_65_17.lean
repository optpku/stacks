/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Noetherian
import StacksCheckRecall

/-!
# Lemma 15.65.17

@stack 066E

Over a Noetherian ring, pseudo-coherence is characterized by bounded-above finite homology; for
modules it is equivalent to finite generation.
-/

open CategoryTheory
open DerivedCategory.TStructure

universe u v

@[stacks 066E "Lemma 15.65.17 (1), Noetherian m-pseudo-coherence criterion"]
#check fun {R : Type u} [Ring R] [IsNoetherianRing R] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v, u} R)) (m : ℤ) ↦
  (CategoryTheory.DerivedCategory.IsMPseudoCoherent.iff_boundedAbove_and_homology_finite_ge K m :
    K.IsMPseudoCoherent m ↔
      (t.minus : ObjectProperty (DerivedCategory (ModuleCat.{v, u} R))) K ∧
        ∀ i : ℤ, m ≤ i →
          Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v, u} R) i).obj K))

@[stacks 066E "Lemma 15.65.17 (2), Noetherian pseudo-coherence criterion"]
#check fun {R : Type u} [Ring R] [IsNoetherianRing R] [Small.{v} R]
    (K : DerivedCategory (ModuleCat.{v, u} R)) ↦
  (CategoryTheory.DerivedCategory.IsPseudoCoherent.iff_boundedAbove_and_homology_finite K :
    K.IsPseudoCoherent ↔
      (t.minus : ObjectProperty (DerivedCategory (ModuleCat.{v, u} R))) K ∧
        ∀ i : ℤ,
          Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{v, u} R) i).obj K))

@[stacks 066E "Lemma 15.65.17 (3), Noetherian pseudo-coherent module criterion"]
#check fun {R : Type u} [Ring R] [IsNoetherianRing R] [Small.{v} R]
    {M : Type v} [AddCommGroup M] [Module R M] ↦
  (Module.isPseudoCoherent_iff_finite (R := R) (M := M) :
    (ModuleCat.of R M).IsPseudoCoherent ↔ Module.Finite R M)
