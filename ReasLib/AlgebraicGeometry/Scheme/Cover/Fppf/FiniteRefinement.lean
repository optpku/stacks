/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf.IntegralRefinement
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Finite refinements of fppf covers

An fppf cover of a quasi-compact and quasi-separated scheme can be refined by an open cover
after pullback along a surjective finite morphism of finite presentation.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.FppfCover

/-- Every fppf cover of a quasi-compact and quasi-separated scheme is refined by the pushforward
of an open cover along a surjective finite morphism of finite presentation. -/
theorem exists_surjective_finite_refinement
    {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (𝒰 : FppfCover.{u, v} S) :
    ∃ (S' : Scheme.{u}) (p : S' ⟶ S) (h_surjective : Surjective p)
      (h_finite : IsFinite p)
      (h_finitePresentation : Scheme.Hom.FinitePresentation p)
      (𝒱 : S'.OpenCover.{u}),
      Nonempty
        (PreZeroHypercover.Hom (𝒱.toPreZeroHypercover.pushforward p) 𝒰.toPreZeroHypercover) := sorry

end AlgebraicGeometry.FppfCover
