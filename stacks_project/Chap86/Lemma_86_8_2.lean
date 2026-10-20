/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.ProperFlat
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

noncomputable section

universe u

/- Lemma 86.8.2: if `Y` is a quasi-compact and quasi-separated algebraic space over a
scheme `S` and `f : X ⟶ Y` is proper, flat, and of finite presentation, then the
canonical comparison 86.7.0.1, `Lf^*K ⊗^L a(𝒪_Y) ⟶ a(K)`, is an isomorphism for
every `K` in `DerivedQCoh Y`. -/
@[stacks 0E5U] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pullbackTensorDualityMap_isIso_of_proper_flat :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
      [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
      (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X)
      (aAdjunction : pushforwardCohomologyIn f ⊣ a)
      (K : DerivedQCoh Y),
      IsIso (pullbackTensorDualityMap f a aAdjunction K))
