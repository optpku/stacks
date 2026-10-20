/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.StandardZariskiCover

@[expose] public section

open AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.Scheme.OpenCover

/-- Every open cover of an affine scheme admits a finite standard Zariski refinement whose
component maps into the selected members of the original cover are open immersions. -/
@[stacks 020Q]
theorem exists_standardRefinement {T : Scheme.{u}} [IsAffine T] (𝒰 : T.OpenCover.{v}) :
    ∃ (𝒱 : T.StandardZariskiCover.{u, w})
      (f : CategoryTheory.Precoverage.ZeroHypercover.Hom
        (precoverage @IsOpenImmersion) 𝒱.toOpenCover 𝒰),
      ∀ j : 𝒱.index, IsOpenImmersion (f.h₀ j) := sorry

end AlgebraicGeometry.Scheme.OpenCover
