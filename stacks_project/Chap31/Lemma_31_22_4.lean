/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeRegularImmersion.FlatFinitePresentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

/- Lemma 31.22.4 (1): a relative quasi-regular immersion over a flat locally finitely
presented morphism is a regular immersion. -/
@[stacks 063U] #check
  (AlgebraicGeometry.RelativeQuasiRegularImmersion.isRegularImmersion_of_flat_locallyOfFinitePresentation :
    ∀ {X S Z : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}
      [AlgebraicGeometry.Flat f] [AlgebraicGeometry.LocallyOfFinitePresentation f]
      [AlgebraicGeometry.RelativeQuasiRegularImmersion f i],
      AlgebraicGeometry.IsRegularImmersion i)

/- Lemma 31.22.4 (2): after any base change, the induced immersion remains a regular
immersion. -/
@[stacks 063U] #check
  (AlgebraicGeometry.RelativeQuasiRegularImmersion.isRegularImmersion_pullback_snd_of_flat_locallyOfFinitePresentation :
    ∀ {X S S' Z : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}
      [AlgebraicGeometry.Flat f] [AlgebraicGeometry.LocallyOfFinitePresentation f]
      [AlgebraicGeometry.RelativeQuasiRegularImmersion f i] (g : S' ⟶ S),
      AlgebraicGeometry.IsRegularImmersion (pullback.snd i (pullback.fst f g)))
