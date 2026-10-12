/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf.EtaleFiniteLocallyFreeRefinement
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

/- Lemma 37.48.1: every fppf cover of a scheme has a refinement whose maps factor,
with a common index, as surjective finite locally free morphisms followed by an étale
covering family. -/
@[stacks 0DET] #check
  (AlgebraicGeometry.FppfCover.exists_etale_finiteLocallyFreeRefinement :
    ∀ {S : Scheme.{u}} (𝒰 : FppfCover.{u, v} S),
      ∃ (𝒱 : S.Cover.{max u v} Scheme.etalePrecoverage)
        (V : 𝒱.I₀ → Scheme.{u})
        (π : ∀ a, V a ⟶ 𝒱.X a)
        (_ : ∀ a, Surjective (π a))
        (_ : ∀ a, IsFiniteLocallyFree (π a)),
        let 𝒲 := 𝒱.toPreZeroHypercover.bind
          (fun a ↦ PreZeroHypercover.singleton (π a))
        𝒲.presieve₀ ∈ Scheme.fppfPrecoverage.coverings S ∧
          Nonempty (PreZeroHypercover.Hom 𝒲 𝒰.toPreZeroHypercover))
