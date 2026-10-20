/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf.LocallyQuasiFiniteRefinement
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.EtaleNeighborhood

/-!
# Étale and finite locally free refinements of fppf covers

Every fppf cover of a scheme admits a refinement which factors through an étale
cover by surjective finite locally free morphisms.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.FppfCover

/-- Every fppf cover of a scheme has a refining fppf family whose morphisms factor through an
étale covering family by surjective finite locally free morphisms. -/
@[stacks 0DET]
theorem exists_etale_finiteLocallyFreeRefinement
    {S : Scheme.{u}} (𝒰 : FppfCover.{u, v} S) :
    ∃ (𝒱 : S.Cover.{max u v} Scheme.etalePrecoverage)
      (V : 𝒱.I₀ → Scheme.{u})
      (π : ∀ a, V a ⟶ 𝒱.X a)
      (_ : ∀ a, Surjective (π a))
      (_ : ∀ a, IsFiniteLocallyFree (π a)),
      let 𝒲 := 𝒱.toPreZeroHypercover.bind
        (fun a ↦ PreZeroHypercover.singleton (π a))
      𝒲.presieve₀ ∈ Scheme.fppfPrecoverage.coverings S ∧
        Nonempty (PreZeroHypercover.Hom 𝒲 𝒰.toPreZeroHypercover) := sorry

end AlgebraicGeometry.FppfCover
