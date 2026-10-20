/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward.VectorBundleLocus
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Lemma 75.26.5: For a proper, flat, finitely presented morphism and a finitely
presented module flat over the target, every integer degree and rank determine an
open subspace characterized by the base-changed derived pushforward being a finite
locally free module of that rank placed in that degree. -/
@[stacks 0E6A] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.exists_pushforwardVectorBundleLocus :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
      (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f]
      (F : X.Modules) (hF_fp : F.IsFinitePresentation) (hF_flat : Modules.flatOver F f)
      (i r : ℤ),
      ∃ V : OpenSubspace Y, ∀ {T : AlgebraicSpace S} (g : T ⟶ Y),
        (∃ lift : T ⟶ V.X, lift ≫ V.ι = g) ↔
          ModuleDerived.IsVectorBundleOfRankInDegree
            (ModuleDerived.baseChangeDerivedPushforward f g F) i r)
