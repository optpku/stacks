/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf.ZariskiFiniteLocallyFreeRefinement
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Integral.Extension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Integral.Product
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Surjective.Product

/-!
# Integral refinements of fppf covers

An arbitrary fppf cover can be refined by an open cover after pullback along a
surjective integral morphism.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.FppfCover

/-- Every fppf cover of a scheme is refined by the pushforward of an open cover
along a surjective integral morphism. -/
theorem exists_surjective_integral_refinement
    {S : Scheme.{u}} (𝒰 : FppfCover.{u, v} S) :
    ∃ (S' : Scheme.{u}) (p : S' ⟶ S) (h_surjective : Surjective p)
      (h_integral : IsIntegralHom p) (𝒱 : S'.OpenCover.{u}),
      Nonempty
        (PreZeroHypercover.Hom (𝒱.toPreZeroHypercover.pushforward p) 𝒰.toPreZeroHypercover) := sorry

end AlgebraicGeometry.FppfCover
