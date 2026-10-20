/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage.Coherent

/-!
# Lemma 69.20.2

Every higher direct image of a coherent module along a proper morphism of algebraic
spaces to a locally Noetherian algebraic space is coherent.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 69.20.2: if `f : X ⟶ Y` is a proper morphism of algebraic spaces over a scheme
`S` with `Y` locally Noetherian, and `F` is a coherent `𝒪_X`-module, then
`higherDirectImage f F i` is a coherent `𝒪_Y`-module for every `i : ℕ`. -/
@[stacks 08AR] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.higherDirectImage_isCoherent_of_proper :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    [IsLocallyNoetherian Y] [Abelian X.Modules] [Abelian Y.Modules]
    [HasInjectiveResolutions X.Modules] (F : X.Modules) [F.IsCoherent]
    (i : ℕ), (higherDirectImage f F i).IsCoherent)

end AlgebraicGeometry.AlgebraicSpace.Modules
