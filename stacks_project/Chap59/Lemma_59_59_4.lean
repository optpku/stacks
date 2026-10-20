/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.SmallEtaleQuasicoherent

import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Etale.Small

universe u

/- Lemma 59.59.4: Let `R` be a local ring of dimension `0` and
`S = Spec (CommRingCat.of R)`. Every `𝒪_S`-module on the small étale site of `S`
is quasi-coherent. -/
@[stacks 0D1W]
#check (AlgebraicGeometry.Scheme.AssociatedModule.SmallEtaleQuasicoherent.all_isQuasicoherent_of_isLocalRing_of_ringKrullDim_eq_zero :
    ∀ (R : Type u) [CommRing R] [IsLocalRing R],
      ringKrullDim R = 0 →
        ∀ F : RingedSite.ModuleCat.{u}
          (ringedSite (Spec (CommRingCat.of R))),
          F.IsQuasicoherent)
