/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.SmoothCover
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory.Limits

universe u

/- Lemma 31.21.11: a Koszul-regular closed immersion becomes regular after pullback along some
smooth surjective morphism. -/
@[stacks 0692] #check
  (AlgebraicGeometry.IsKoszulRegularClosedImmersion.exists_smooth_surjective_regularImmersion_pullback :
    ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsKoszulRegularClosedImmersion i],
      ∃ (X' : Scheme.{u}) (f : X' ⟶ X),
        Surjective f ∧ Smooth f ∧ IsRegularImmersion (pullback.snd i f))
