module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood.FiniteLocallyFreeCover

/-!
# Finite locally free refinements of étale covers

Every étale cover has a refinement assembled from Zariski open covers and surjective
finite locally free morphisms.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.Cover

/-- Every étale cover of a scheme is refined by a Zariski open cover, followed over each
member by a surjective finite locally free morphism and then another Zariski open cover. -/
theorem exists_finiteLocallyFreeRefinement {S : Scheme.{u}}
    (𝒰 : S.Cover.{v} Scheme.etalePrecoverage) :
    ∃ (𝒱 : S.OpenCover.{u}) (W : 𝒱.I₀ → Scheme.{u})
      (π : ∀ j, W j ⟶ 𝒱.X j)
      (hπsurj : ∀ j, Surjective (π j))
      (hπflf : ∀ j, IsFiniteLocallyFree (π j))
      (𝒲 : ∀ j, (W j).OpenCover.{u}),
      Nonempty
        (PreZeroHypercover.Hom
          (𝒱.toPreZeroHypercover.bind fun j ↦
            (𝒲 j).toPreZeroHypercover.pushforward (π j))
          𝒰.toPreZeroHypercover) := sorry

end AlgebraicGeometry.Scheme.Cover
