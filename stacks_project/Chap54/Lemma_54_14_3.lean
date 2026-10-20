/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Resolution
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 54.14.3: for a two-dimensional Noetherian normal local ring, existence of a
resolution of its spectrum implies existence of a resolution by normalized blowups. -/
@[stacks 0BGM] #check
  (AlgebraicGeometry.Scheme.hasResolutionByNormalizedBlowups_of_existsResolution :
    ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalRing A]
      (h_dim : ringKrullDim A = 2)
      (h_resolution :
        ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)), IsResolution f),
      HasResolutionByNormalizedBlowups (Spec (.of A))
        ((PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).trans h_dim))

end AlgebraicGeometry.Scheme
