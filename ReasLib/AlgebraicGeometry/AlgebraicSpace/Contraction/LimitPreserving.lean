/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Functor
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Extension.Conditions

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Over

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- The compatible-triple functor of a contraction situation preserves directed
inverse limits of affine schemes whose stages and limit are locally Noetherian. -/
theorem preservesDirectedAffineLimits (σ : ContractionSituation S) :
    Extension.PreservesDirectedAffineLimits (locallyNoetherian S) σ.functor :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
