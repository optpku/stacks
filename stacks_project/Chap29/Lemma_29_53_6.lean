/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.AlgebraicGeometry.Normalization
import StacksCheckRecall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
variable (U : X.Opens)

/- Lemma 29.53.6: for an arbitrary open subscheme `U` of `X`, the normalization of the
pullback `pullback.snd f U.ι` is canonically isomorphic to the pullback of
`f.fromNormalization` along `U.ι`. -/
@[stacks 035K] #check
  (AlgebraicGeometry.Scheme.Hom.instIsIsoNormalizationPullbackOfSmooth (f := f) (g := U.ι) :
    CategoryTheory.IsIso (f.normalizationPullback U.ι))

end AlgebraicGeometry.Scheme.Hom
