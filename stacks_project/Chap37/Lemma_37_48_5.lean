/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf.IntegralRefinement
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.FppfCover

/- Lemma 37.48.5: every fppf cover of a scheme is refined by the pushforward of an open
cover along a surjective integral morphism. -/
@[stacks 0CNZ] #check
  (AlgebraicGeometry.FppfCover.exists_surjective_integral_refinement :
    ∀ {S : Scheme.{u}} (𝒰 : FppfCover.{u, v} S),
      ∃ (S' : Scheme.{u}) (p : S' ⟶ S) (h_surjective : Surjective p)
        (h_integral : IsIntegralHom p) (𝒱 : S'.OpenCover.{u}),
        Nonempty
          (PreZeroHypercover.Hom
            (𝒱.toPreZeroHypercover.pushforward p) 𝒰.toPreZeroHypercover))

end AlgebraicGeometry.FppfCover
