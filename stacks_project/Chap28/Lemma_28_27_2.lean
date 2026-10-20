/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiAffine.Immersion
import StacksCheckRecall

/-!
# Lemma 28.27.2

Quasi-affineness is preserved by quasi-compact immersions.

@stack 0BCK
-/

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 28.27.2: A quasi-compact immersion into a quasi-affine scheme has
quasi-affine source. -/
@[stacks 0BCK] #check
  (AlgebraicGeometry.Scheme.IsQuasiAffine.of_isImmersion_of_quasiCompact :
    ∀ {X X' : Scheme.{u}} {i : X' ⟶ X},
      X.IsQuasiAffine → IsImmersion i → QuasiCompact i → X'.IsQuasiAffine)
