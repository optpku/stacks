module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf.ZariskiFiniteLocallyFreeRefinement
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

/- Lemma 37.48.2: every fppf cover of a scheme is refined by an outer Zariski cover,
surjective finite locally free morphisms, inner Zariski covers, and a second family of
surjective finite locally free morphisms. -/
@[stacks 05WN] #check
  (AlgebraicGeometry.FppfCover.exists_zariski_finiteLocallyFreeRefinement :
    ∀ {S : Scheme.{u}} (𝒰 : FppfCover.{u, v} S),
      ∃ (𝒱 : S.OpenCover.{u}) (W : 𝒱.I₀ → Scheme.{u})
        (π : ∀ j, W j ⟶ 𝒱.X j)
        (hπsurj : ∀ j, Surjective (π j))
        (hπflf : ∀ j, IsFiniteLocallyFree (π j))
        (𝒲 : ∀ j, (W j).OpenCover.{u})
        (T : ∀ j, (𝒲 j).I₀ → Scheme.{u})
        (τ : ∀ j k, T j k ⟶ (𝒲 j).X k)
        (hτsurj : ∀ j k, Surjective (τ j k))
        (hτflf : ∀ j k, IsFiniteLocallyFree (τ j k)),
        let 𝒯 := 𝒱.toPreZeroHypercover.bind (fun j ↦
          ((𝒲 j).toPreZeroHypercover.bind (fun k ↦
            PreZeroHypercover.singleton (τ j k))).pushforward (π j))
        𝒯.presieve₀ ∈ Scheme.fppfPrecoverage.coverings S ∧
          Nonempty (PreZeroHypercover.Hom 𝒯 𝒰.toPreZeroHypercover))
