/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap48.Lemma_48_3_1_Instances
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.RightAdjoint.BoundedBelow
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 48.3.5: a chosen right adjoint to derived quasicoherent pushforward along a
morphism of quasi-compact quasi-separated schemes has a uniform lower cohomological bound.
Here `K.obj.IsGE (c + 1)` means that `Hⁱ(K) = 0` for `i ≤ c`, and the conclusion gives
vanishing for `a.obj K` in degrees `i ≤ c - N`. -/
@[stacks 0A9I] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.rightAdjoint_uniformLowerBound :
    ∀ {X Y : Scheme.{u}},
      [CompactSpace X] → [QuasiSeparatedSpace X] →
      [CompactSpace Y] → [QuasiSeparatedSpace Y] →
      (f : X ⟶ Y) →
      (a : AlgebraicGeometry.Scheme.DerivedQCoh Y ⥤
        AlgebraicGeometry.Scheme.DerivedQCoh X) →
      (AlgebraicGeometry.Scheme.DerivedQCoh.pushforward f ⊣ a) →
      ∃ N : ℤ, ∀ (K : AlgebraicGeometry.Scheme.DerivedQCoh Y) (c : ℤ),
        K.obj.IsGE (c + 1) → (a.obj K).obj.IsGE (c - N + 1))
