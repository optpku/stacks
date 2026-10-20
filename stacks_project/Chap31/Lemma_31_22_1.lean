/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeRegularImmersion.BaseChange
import StacksCheckRecall

universe u

/- Lemma 31.22.1 (1): relative `H_1`-regular immersions remain `H_1`-regular after arbitrary
base change. -/
@[stacks 063R] #check
  (AlgebraicGeometry.RelativeH1RegularImmersion.h1RegularImmersion_pullback_snd :
    ∀ {X S S' Z : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}
      [AlgebraicGeometry.RelativeH1RegularImmersion f i] (g : S' ⟶ S),
      AlgebraicGeometry.IsH1RegularImmersion
        (CategoryTheory.Limits.pullback.snd i (CategoryTheory.Limits.pullback.fst f g)))

/- Lemma 31.22.1 (2): relative quasi-regular immersions remain quasi-regular after arbitrary
base change. -/
@[stacks 063R] #check
  (AlgebraicGeometry.RelativeQuasiRegularImmersion.quasiRegularImmersion_pullback_snd :
    ∀ {X S S' Z : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}
      [AlgebraicGeometry.RelativeQuasiRegularImmersion f i] (g : S' ⟶ S),
      AlgebraicGeometry.IsQuasiRegularImmersion
        (CategoryTheory.Limits.pullback.snd i (CategoryTheory.Limits.pullback.fst f g)))
