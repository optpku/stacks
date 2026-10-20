/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiAffine.Characterization
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 28.18.4: A scheme is quasi-affine if and only if its canonical morphism to the spectrum
of its global sections is a quasi-compact open immersion. -/
@[stacks 01P9] #check
  (AlgebraicGeometry.Scheme.isQuasiAffine_iff_toSpecΓ :
    ∀ X : Scheme.{u}, X.IsQuasiAffine ↔ QuasiCompact X.toSpecΓ ∧ IsOpenImmersion X.toSpecΓ)
