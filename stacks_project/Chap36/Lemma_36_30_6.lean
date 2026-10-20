/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Associated.Limit

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 36.30.6: for a proper, flat, finitely presented morphism `f : X ⟶ Spec R`
and a sequential inverse system of `R`-modules with epimorphic transitions, the canonical
map from the associated module of `limit M` to `DQ_X` of the limit of the associated modules
is an isomorphism. -/
@[stacks 0D2Q] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.Associated.limitComparison_isIso :
    ∀ {R : Type u} [CommRing R] {X : Scheme.{u}}
      (f : X ⟶ Spec (CommRingCat.of R)) [Flat f] [IsProper f]
      [Scheme.Hom.FinitePresentation f] (M : SequentialInverseSystem (ModuleCat.{u} R))
      [∀ n : ℕ, Epi (SequentialInverseSystem.transitionMap M (Nat.le_succ n))],
      IsIso (AlgebraicGeometry.Scheme.DerivedQCoh.Associated.limitComparison f M))
