/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf.FiniteRefinement
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

/- Lemma 37.48.6: every fppf cover of a quasi-compact and quasi-separated scheme is
refined by the pushforward of an open cover along a surjective finite morphism of finite
presentation. -/
@[stacks 0CP0] #check
  (AlgebraicGeometry.FppfCover.exists_surjective_finite_refinement :
    {S : Scheme.{u}} → [CompactSpace S] → [QuasiSeparatedSpace S] →
      (𝒰 : FppfCover.{u, v} S) →
        ∃ (S' : Scheme.{u}) (p : S' ⟶ S) (h_surjective : Surjective p)
          (h_finite : IsFinite p)
          (h_finitePresentation : Scheme.Hom.FinitePresentation p)
          (𝒱 : S'.OpenCover.{u}),
          Nonempty
            (PreZeroHypercover.Hom
              (𝒱.toPreZeroHypercover.pushforward p) 𝒰.toPreZeroHypercover))
