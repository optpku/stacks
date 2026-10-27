/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlongSubspace

/-!
# Completion along a closed subspace

The shared owners supply the infinitesimal neighbourhoods, their completion in
fppf sheaves, and the canonical maps. Sections of the completion fppf-locally
factor through a neighbourhood, with its order allowed to vary over the cover.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace

universe u

attribute [instance] ClosedSubspace.isClosedImmersion

#check @ClosedSubspace.isClosedImmersion

#check @Hom.InfinitesimalNeighbourhood.ideal
#check @Hom.InfinitesimalNeighbourhood.ideal_eq_pow
#check @Hom.InfinitesimalNeighbourhood.space
#check @Hom.InfinitesimalNeighbourhood.space_eq_subscheme
#check @Hom.InfinitesimalNeighbourhood.toAmbient

#check @factorsThroughNeighbourhood
#check @factorsThroughNeighbourhood_iff
#check @factorsThroughNeighbourhood_toAmbient
#check @factorsThroughNeighbourhood_map
#check @fppfLocallyFactorsThroughNeighbourhood
#check @fppfLocallyFactorsThroughNeighbourhood_iff
#check @fppfLocallyFactorsThroughNeighbourhood.of_stage
#check @fppfLocallyFactorsThroughNeighbourhood_map

#check @completionAlongSubspace

/- The completion consists of sections that fppf-locally factor through some
infinitesimal neighbourhood. -/
#check (completionAlongSubspace_eq :
    ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X)
      [IsClosedImmersion i] (U : (Over S)ᵒᵖ),
      (completionAlongSubspace i).obj U =
        { x : X.functorOfPoints.obj U // fppfLocallyFactorsThroughNeighbourhood i x })

#check @completionAlongSubspace.ι
#check @completionAlongSubspace.ι_app
#check @completionAlongSubspace.exists_lift
#check @completionAlongSubspace.fromStage
#check @completionAlongSubspace.fromStage_app
#check @completionAlongSubspace.fromStage_comp
