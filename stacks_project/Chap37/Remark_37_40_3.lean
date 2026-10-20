/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Etale.FiniteLocallyFreeRefinement
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

/- Remark 37.40.3: every étale cover of a scheme is refined by a Zariski open cover,
followed over each member by a surjective finite locally free morphism and then another
Zariski open cover. -/
@[stacks 02LI] #check
  (AlgebraicGeometry.Scheme.Cover.exists_finiteLocallyFreeRefinement :
    ∀ {S : Scheme.{u}} (𝒰 : S.Cover.{v} Scheme.etalePrecoverage),
      ∃ (𝒱 : S.OpenCover.{u}) (W : 𝒱.I₀ → Scheme.{u})
        (π : ∀ j, W j ⟶ 𝒱.X j)
        (hπsurj : ∀ j, Surjective (π j))
        (hπflf : ∀ j, IsFiniteLocallyFree (π j))
        (𝒲 : ∀ j, (W j).OpenCover.{u}),
        Nonempty
          (PreZeroHypercover.Hom
            (𝒱.toPreZeroHypercover.bind fun j ↦
              (𝒲 j).toPreZeroHypercover.pushforward (π j))
            𝒰.toPreZeroHypercover))
