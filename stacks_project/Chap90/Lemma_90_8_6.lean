/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothPowerSeries
import StacksCheckRecall

/-!
# Smoothness of restricted coyoneda maps

A morphism in `CompleteLocalAlgCat Λ k` induces a smooth map of restricted coyoneda
functors on `ArtinianLocalAlgCat` if and only if the target is a finite-variable
power series ring over the source.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 90.8.6: a morphism of complete local algebras induces a smooth morphism
of restricted coyoneda functors exactly when it is a power series extension. -/
@[stacks 06HL] #check (CompleteLocalAlgCat.restrictedCoyonedaMap_isSmooth_iff :
  ∀ {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S),
    CategoryTheory.NatTrans.IsSmooth (CompleteLocalAlgCat.restrictedCoyonedaMap f) ↔
      CompleteLocalAlgCat.IsPowerSeriesOver f)
