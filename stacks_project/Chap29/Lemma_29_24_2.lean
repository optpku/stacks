/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Submersive
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X Y T : Scheme.{u}}

/- Lemma 29.24.2 [0CES]: base change of a universally submersive morphism is supplied by the
neutral `UniversallySubmersive.pullback_snd` API. -/
@[stacks 0CES]
#check (AlgebraicGeometry.UniversallySubmersive.pullback_snd :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {T : Scheme.{u}},
    UniversallySubmersive f → ∀ g : T ⟶ Y, UniversallySubmersive (pullback.snd f g))

end AlgebraicGeometry
