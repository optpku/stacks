/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Functor
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Noetherian.RimSchlessinger

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

/-- The functor of compatible open and formal triples associated to a contraction
situation satisfies the Rim-Schlessinger condition. -/
theorem hasRimSchlessinger {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    (σ : ContractionSituation S) :
    Scheme.Over.HasRimSchlessinger σ.functor := sorry

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
